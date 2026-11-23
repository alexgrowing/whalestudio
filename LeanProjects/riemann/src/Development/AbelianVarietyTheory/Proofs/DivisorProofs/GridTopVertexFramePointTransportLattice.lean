import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopExt

open Formalism.UG GlobalTheory.AutFunCounterexample

variable {D : D7} {A B : HSp D}

local notation "σ" => (D.sp.cm.sig : D.host.E →+* D.host.E)

abbrev emb (d : HermitianOrthogonalExtensionData A B 1 1) : Matrix (Fin B.rank) (Fin A.rank) D.host.E := frameMat B A d.ι

def prj (d : HermitianOrthogonalExtensionData A B 1 1) : Matrix (Fin A.rank) (Fin B.rank) D.host.E := A.gram⁻¹ * (cT σ (emb d) * B.gram)

def crd (d : HermitianOrthogonalExtensionData A B 1 1) : Matrix (Fin 1) (Fin B.rank) D.host.E := cT σ d.a * B.gram

theorem gram_unit (A : HSp D) : IsUnit A.gram.det := (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit

theorem emb_gram (d : HermitianOrthogonalExtensionData A B 1 1) : cT σ (emb d) * B.gram * emb d = A.gram := gram_pull B A d.ι d.isom

theorem orthogonalExtension_conjTranspose_mul_gram_mul_eq_one (d : HermitianOrthogonalExtensionData A B 1 1) : cT σ d.a * B.gram * d.a = 1 := by
  rw [d.gram]
  ext i j
  fin_cases i; fin_cases j
  simp [antiDiagonalSignGramMatrix]

theorem prj_emb (d : HermitianOrthogonalExtensionData A B 1 1) : prj d * emb d = 1 := by
  rw [prj, Matrix.mul_assoc, emb_gram, Matrix.nonsing_inv_mul _ (gram_unit A)]

theorem orthogonalSumProjection_mul_auxiliary (d : HermitianOrthogonalExtensionData A B 1 1) : prj d * d.a = 0 := by
  rw [prj, Matrix.mul_assoc, d.perp, Matrix.mul_zero]

theorem coefficient_mul_a_eq_one (d : HermitianOrthogonalExtensionData A B 1 1) : crd d * d.a = 1 := orthogonalExtension_conjTranspose_mul_gram_mul_eq_one d

theorem crd_emb (d : HermitianOrthogonalExtensionData A B 1 1) : crd d * emb d = 0 := by
  have h := congrArg (cT σ) d.perp
  rw [cT_mul, cT_mul, gram_herm, cT_cT] at h
  have h0 : cT σ (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) = 0 := by
    ext i j; simp [cT]
  rw [h0, ← Matrix.mul_assoc] at h
  exact h

theorem split (d : HermitianOrthogonalExtensionData A B 1 1) : emb d * prj d + d.a * crd d = 1 := by
  have e : Fin A.rank ⊕ Fin 1 ≃ Fin B.rank := finSumFinEquiv.trans (finCongr d.rank)
  have h : (Matrix.fromRows (prj d) (crd d)) * (Matrix.fromCols (emb d) d.a) = 1 := by
    rw [Matrix.fromRows_mul_fromCols, prj_emb, orthogonalSumProjection_mul_auxiliary, crd_emb, coefficient_mul_a_eq_one, Matrix.fromBlocks_one]
  have := (Matrix.mul_eq_one_comm_of_equiv e).1 h
  rwa [Matrix.fromCols_mul_fromRows] at this

theorem split_map {R : Type} [CommRing R] (φ : D.host.E →+* R) (d : HermitianOrthogonalExtensionData A B 1 1) :
    (emb d).map φ * (prj d).map φ + d.a.map φ * (crd d).map φ = 1 := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add φ), split, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_ext {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') {n r : ℕ} (P : Matrix (Fin n) (Fin r) R)
    (Q : Matrix (Fin r) (Fin n) R) (h : Matrix (Fin r) (Fin r) R) :
    (1 + P * (h - 1) * Q).map ρ = 1 + P.map ρ * (h.map ρ - 1) * Q.map ρ := by
  rw [Matrix.map_add _ (map_add ρ), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub ρ),
    Matrix.map_one ρ (map_zero ρ) (map_one ρ), Matrix.map_one ρ (map_zero ρ) (map_one ρ)]

def extM {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (h : Matrix (Fin r) (Fin r) R) : Matrix (Fin n) (Fin n) R := 1 + P * (h - 1) * Q

theorem exists_ext {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (σ' : E →ₐ[F] E)
    {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin n) (Fin r) E)
    (Q : Matrix (Fin r) (Fin n) E) (q1 : J * P = cT (σ' : E →+* E) Q * G) (q2 : cT (σ' : E →+* E) P * J = G * Q)
    (q3 : Q * P = 1) (h : HR R σ' G) :
    ∃ g : HR R σ' J, g.1.1 = 1 + P.map (inclR (F := F) R) * (h.1.1 - 1) * Q.map (inclR (F := F) R) := by
  set φ : E →+* R ⊗[F] E := inclR (F := F) R
  have m3 : Q.map φ * P.map φ = 1 := by
    rw [← Matrix.map_mul, q3, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨⟨1 + P.map φ * (h.1.1 - 1) * Q.map φ, 1 + P.map φ * (h.1.inv - 1) * Q.map φ,
    ext_mul _ _ m3 _ _ h.1.val_inv, ext_mul _ _ m3 _ _ h.1.inv_val⟩, ?_⟩, rfl⟩
  refine ext_unitary (sigR R σ') (J.map φ) (G.map φ) _ _ ?_ ?_ m3 _ h.2
  · rw [cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, q1]
  · rw [cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, q2]

theorem exists_pt (d : HermitianOrthogonalExtensionData A B 1 1) (h : GA D A) :
    ∃ g : GA D B, (matHom B g).1 = extM ((emb d).map (incA D)) ((prj d).map (incA D)) (matHom A h).1 := by
  have q2 : cT σ (emb d) * B.gram = A.gram * prj d := by
    rw [prj, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_unit A), Matrix.one_mul]
  have q1 : B.gram * emb d = cT σ (prj d) * A.gram := by
    have := congrArg (cT σ) q2
    rwa [cT_mul, cT_mul, gram_herm, cT_cT, gram_herm] at this
  exact exists_ext (R := AF D.host.F) D.sp.cm.sig B.gram A.gram (emb d) (prj d) q1 q2 (prj_emb d) h

section Ext

variable {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
  (h : Matrix (Fin r) (Fin r) R)

theorem extM_sub_one : extM P Q h - 1 = P * (h - 1) * Q := by
  rw [extM, add_sub_cancel_left]

theorem extM_mul (hQ : Q * P = 1) : extM P Q h * P = P * h := by
  rw [extM, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQ, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one,
    add_sub_cancel]

theorem extM_mulVec {v : Fin n → R} (hv : Q *ᵥ v = 0) : extM P Q h *ᵥ v = v := by
  rw [extM, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero]

theorem prj_extM (hQ : Q * P = 1) : Q * extM P Q h = h * Q := by
  rw [extM, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul, Matrix.sub_mul,
    Matrix.one_mul, add_sub_cancel]

theorem crd_extM {c : ℕ} (C : Matrix (Fin c) (Fin n) R) (hC : C * P = 0) : C * extM P Q h = C := by
  rw [extM, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hC, Matrix.zero_mul, Matrix.zero_mul,
    add_zero]

theorem extM_one : extM P Q 1 = 1 := by
  simp [extM]

theorem extM_map {R' : Type} [CommRing R'] (ρ : R →+* R') : (extM P Q h).map ρ = extM (P.map ρ) (Q.map ρ) (h.map ρ) :=
  map_ext ρ P Q h

theorem extM_supp (ε : R) (hs : ∀ i j, ε * (h - 1) i j = (h - 1) i j) (i j : Fin n) :
    ε * (extM P Q h - 1) i j = (extM P Q h - 1) i j := by
  have e : ε • (h - 1) = h - 1 := Matrix.ext fun i j => hs i j
  have : ε • (extM P Q h - 1) = extM P Q h - 1 := by
    rw [extM_sub_one, ← Matrix.smul_mul, ← Matrix.mul_smul, e]
  exact congrFun (congrFun this i) j

end Ext

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "ιf" => inclE (F := F) (E := E) (Formalism.L2.Herm.Af F)
local notation "hat" => Formalism.L2.Herm.hatL (F := F) (E := E)

theorem hat_mulVec {p q : ℕ} (N : Matrix (Fin p) (Fin q) E) {Λ : Submodule (𝓞 E) (Fin q → E)}
    {Λ' : Submodule (𝓞 E) (Fin p → E)} (h : ∀ y ∈ Λ, N *ᵥ y ∈ Λ') {v} (hv : v ∈ hat Λ) :
    N.map ιf *ᵥ v ∈ hat Λ' := by
  refine Submodule.span_induction (p := fun v _ => N.map ιf *ᵥ v ∈ hat Λ') ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨N *ᵥ x, h x hx, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  · rw [Matrix.mulVec_zero]; exact zero_mem _
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add]; exact add_mem hx hy
  · intro s x _ hx
    have : N.map ιf *ᵥ (s • x) = s • (N.map ιf *ᵥ x) := by
      rw [Subring.smul_def, Subring.smul_def, Matrix.mulVec_smul]
    rw [this]
    exact Submodule.smul_mem _ s hx

variable {n k c : ℕ} {M : Matrix (Fin n) (Fin k) E} {a : Matrix (Fin n) (Fin c) E} {Q : Matrix (Fin k) (Fin n) E}
  {C : Matrix (Fin c) (Fin n) E}

theorem mem_hat_sum (QM : Q * M = 1) (Qa : Q * a = 0) (CM : C * M = 0) (Ca : C * a = 1)
    (sp : M.map ιf * Q.map ιf + a.map ιf * C.map ιf = 1) {Λ : Submodule (𝓞 E) (Fin k → E)}
    {Λ₁ : Submodule (𝓞 E) (Fin c → E)} {Λs : Submodule (𝓞 E) (Fin n → E)}
    (hs : ∀ x, x ∈ Λs ↔ ∃ y ∈ Λ, ∃ u ∈ Λ₁, x = M *ᵥ y + a *ᵥ u) (v) :
    v ∈ hat Λs ↔ Q.map ιf *ᵥ v ∈ hat Λ ∧ C.map ιf *ᵥ v ∈ hat Λ₁ := by
  constructor
  · intro hv
    refine ⟨hat_mulVec _ ?_ hv, hat_mulVec _ ?_ hv⟩
    · intro x hx
      obtain ⟨y, hy, u, -, rfl⟩ := (hs x).1 hx
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, QM, Qa, Matrix.one_mulVec,
        Matrix.zero_mulVec, add_zero]
      exact hy
    · intro x hx
      obtain ⟨y, -, u, hu, rfl⟩ := (hs x).1 hx
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, CM, Ca, Matrix.one_mulVec,
        Matrix.zero_mulVec, zero_add]
      exact hu
  · rintro ⟨h1, h2⟩
    have e : v = M.map ιf *ᵥ (Q.map ιf *ᵥ v) + a.map ιf *ᵥ (C.map ιf *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, sp, Matrix.one_mulVec]
    rw [e]
    refine add_mem (hat_mulVec _ ?_ h1) (hat_mulVec _ ?_ h2)
    · intro y hy
      exact (hs _).2 ⟨y, hy, 0, zero_mem _, by simp⟩
    · intro u hu
      exact (hs _).2 ⟨0, zero_mem _, u, hu, by simp⟩

theorem hat_transport (QM : Q * M = 1) (Qa : Q * a = 0) (CM : C * M = 0) (Ca : C * a = 1)
    (sp : M.map ιf * Q.map ιf + a.map ιf * C.map ιf = 1) {Λ₀ Λ : Submodule (𝓞 E) (Fin k → E)}
    {Λ₁ : Submodule (𝓞 E) (Fin c → E)} {Λs₀ Λs : Submodule (𝓞 E) (Fin n → E)}
    (hs₀ : ∀ x, x ∈ Λs₀ ↔ ∃ y ∈ Λ₀, ∃ u ∈ Λ₁, x = M *ᵥ y + a *ᵥ u)
    (hs : ∀ x, x ∈ Λs ↔ ∃ y ∈ Λ, ∃ u ∈ Λ₁, x = M *ᵥ y + a *ᵥ u)
    (T : Matrix (Fin k) (Fin k) (E ⊗[F] Formalism.L2.Herm.Af F)) (hT : ∀ w, w ∈ hat Λ₀ ↔ T *ᵥ w ∈ hat Λ) (v) :
    v ∈ hat Λs₀ ↔ extM (M.map ιf) (Q.map ιf) T *ᵥ v ∈ hat Λs := by
  have qm : Q.map ιf * M.map ιf = 1 := by
    rw [← Matrix.map_mul, QM, Matrix.map_one _ (map_zero _) (map_one _)]
  have cm : C.map ιf * M.map ιf = 0 := by
    rw [← Matrix.map_mul, CM]; ext i j; simp
  rw [mem_hat_sum QM Qa CM Ca sp hs₀, mem_hat_sum QM Qa CM Ca sp hs, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    prj_extM _ _ _ qm, crd_extM _ _ _ _ cm, ← Matrix.mulVec_mulVec, hT]

end Lat

def unitLat (D : D7) : Submodule (𝓞 D.host.E) (Fin 1 → D.host.E) where
  carrier := {u | ∀ p, u p ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)}
  zero_mem' := fun p => (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E).zero_mem
  add_mem' := fun hu hv p => (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E).val.add_mem (hu p) (hv p)
  smul_mem' := fun c _ hu p => (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E).val.smul_mem c (hu p)

theorem mem_lat (d : HermitianOrthogonalExtensionData A B 1 1) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (x) :
    x ∈ d.lat Λ (fun _ => 1) ↔ ∃ y ∈ Λ, ∃ u ∈ unitLat D, x = emb d *ᵥ y + d.a *ᵥ u := Iff.rfl

def ixE (d : HermitianOrthogonalExtensionData A B 1 1) : Fin A.rank ⊕ Fin 1 ≃ Fin B.rank := finSumFinEquiv.trans (finCongr d.rank)

theorem ixE_inl (d : HermitianOrthogonalExtensionData A B 1 1) (k) : ixE d (Sum.inl k) = Formalism.L2.Col.Br.iC d.rank.symm k :=
  Fin.ext (by simp [ixE, Formalism.L2.Col.Br.iC])

theorem ixE_inr (d : HermitianOrthogonalExtensionData A B 1 1) (p) : ixE d (Sum.inr p) = Formalism.L2.Col.Br.iL d.rank.symm := by
  have : p = 0 := Subsingleton.elim _ _
  subst this
  exact Fin.ext (by simp [ixE, Formalism.L2.Col.Br.iL])

def frM (d : HermitianOrthogonalExtensionData A B 1 1) (f : Matrix (Fin A.rank) (Fin A.rank) D.host.E) : Matrix (Fin B.rank) (Fin B.rank) D.host.E :=
  (Matrix.fromCols (emb d * f) d.a).submatrix id (ixE d).symm

theorem frM_iC (d : HermitianOrthogonalExtensionData A B 1 1) (f) (i k) : frM d f i (Formalism.L2.Col.Br.iC d.rank.symm k) = (emb d * f) i k := by
  rw [← ixE_inl, frM, Matrix.submatrix_apply, Equiv.symm_apply_apply]; rfl

theorem frM_iL (d : HermitianOrthogonalExtensionData A B 1 1) (f) (i) : frM d f i (Formalism.L2.Col.Br.iL d.rank.symm) = d.a i 0 := by
  rw [← ixE_inr d 0, frM, Matrix.submatrix_apply, Equiv.symm_apply_apply]; rfl

theorem frM_on (d : HermitianOrthogonalExtensionData A B 1 1) (f) (hf : cT σ f * A.gram * f = 1) : cT σ (frM d f) * B.gram * frM d f = 1 := by
  set X := Matrix.fromCols (emb d * f) d.a with hX
  have e1 : cT σ (frM d f) * B.gram * frM d f = (cT σ X * B.gram * X).submatrix (ixE d).symm (ixE d).symm := rfl
  have e2 : cT σ X * B.gram * X = Matrix.fromBlocks 1 0 0 1 := by
    have a1 : cT σ (emb d * f) * B.gram * (emb d * f) = 1 := by
      rw [cT_mul, Matrix.mul_assoc (cT σ f), Matrix.mul_assoc (cT σ f), ← Matrix.mul_assoc _ (emb d), ← Matrix.mul_assoc _ _ f, emb_gram]
      exact hf
    have a2 : cT σ (emb d * f) * B.gram * d.a = 0 := by
      rw [cT_mul, Matrix.mul_assoc (cT σ f), Matrix.mul_assoc (cT σ f), d.perp, Matrix.mul_zero]
    have a3 : cT σ d.a * B.gram * (emb d * f) = 0 := by
      rw [← Matrix.mul_assoc]
      have := crd_emb d
      rw [crd] at this
      rw [this, Matrix.zero_mul]
    have a4 := orthogonalExtension_conjTranspose_mul_gram_mul_eq_one d
    refine Matrix.ext fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · exact congrFun (congrFun a1 i) j
    · exact congrFun (congrFun a2 i) j
    · exact congrFun (congrFun a3 i) j
    · exact congrFun (congrFun a4 i) j
  rw [e1, e2, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

def frG (d : HermitianOrthogonalExtensionData A B 1 1) (f) (hf : cT σ f * A.gram * f = 1) : GL (Fin B.rank) D.host.E :=
  ⟨frM d f, cT σ (frM d f) * B.gram, (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 (frM_on d f hf), frM_on d f hf⟩

theorem colLat_frG (d : HermitianOrthogonalExtensionData A B 1 1) (f : GL (Fin A.rank) D.host.E) (hf : cT σ f.1 * A.gram * f.1 = 1) :
    colLat (frG d f.1 hf) = d.lat (colLat f) fun _ => 1 := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨x, rfl⟩ := (ixE d).surjective j
    rcases x with k | p
    · refine (mem_lat d _ _).2 ⟨fun a => f.1 a k, Submodule.subset_span ⟨k, rfl⟩, 0, zero_mem _, ?_⟩
      funext i
      show frM d f.1 i _ = _
      rw [ixE_inl, frM_iC, Matrix.mulVec_zero, add_zero]
      rfl
    · refine (mem_lat d _ _).2 ⟨0, zero_mem _, 1, fun _ => (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, ?_⟩
      funext i
      show frM d f.1 i _ = _
      rw [ixE_inr, frM_iL, Matrix.mulVec_zero, zero_add]
      simp [Matrix.mulVec, dotProduct]
  · rintro _ ⟨y, hy, u, hu, rfl⟩
    refine add_mem ?_ ?_
    · refine Submodule.span_induction (p := fun y _ => emb d *ᵥ y ∈ colLat (frG d f.1 hf)) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨k, rfl⟩
        refine Submodule.subset_span ⟨Formalism.L2.Col.Br.iC d.rank.symm k, ?_⟩
        funext i
        show frM d f.1 i _ = _
        rw [frM_iC]
        rfl
      · rw [Matrix.mulVec_zero]; exact zero_mem _
      · intro x y _ _ hx hy
        rw [Matrix.mulVec_add]; exact add_mem hx hy
      · intro s x _ hx
        rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ s hx
    · obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hu 0)
      have : d.a *ᵥ u = o • (fun i => (frG d f.1 hf).1 i (Formalism.L2.Col.Br.iL d.rank.symm)) := by
        funext i
        show _ = o • frM d f.1 i _
        rw [frM_iL, Algebra.smul_def, ho, mul_comm]
        simp [Matrix.mulVec, dotProduct]
      rw [this]
      exact Submodule.smul_mem _ o (Submodule.subset_span ⟨_, rfl⟩)

def rhoI (D : D7) : AF D.host.F ⊗[D.host.F] D.host.E →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def rhoF (D : D7) : AF D.host.F ⊗[D.host.F] D.host.E →+* Formalism.IndefR.Lev.EAf D :=
  (Formalism.IndefR.Lev.swapAE D).comp (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem infHom_val (V : HSp D) (g : GA D V) : (infHom V g).1 = ((matHom V g).1).map (rhoI D) := rfl

theorem finE_val (V : HSp D) (g : GA D V) : (Formalism.IndefR.Lev.finE V g).1 = ((matHom V g).1).map (rhoF D) := rfl

theorem rhoF_incA (x : D.host.E) : rhoF D (incA D x) = inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) x := by
  simp [rhoF, Formalism.IndefR.Lev.swapAE, inclR, inclE]

theorem map_incA_rhoF {p q : ℕ} (X : Matrix (Fin p) (Fin q) D.host.E) :
    (X.map (incA D)).map (rhoF D) = X.map (inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) :=
  Matrix.ext fun i j => rhoF_incA (X i j)

set_option maxHeartbeats 2000000 in

theorem top_abs (d : HermitianOrthogonalExtensionData A B 1 1) (S : Finset ℕ) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (Λs : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)) (hΛ : Λs = d.lat Λ fun _ => 1)
    (fr₀ : GL (Fin A.rank) D.host.E) (u₀ : GfC A) (hon : cT σ fr₀.1 * A.gram * fr₀.1 = 1)
    (hsu : ∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u₀.1 ∧ ∀ w ∈ P, Off S w)
    (hl : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr₀) ↔
      (Formalism.IndefR.Lev.finE A u₀.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    ∃ (fr : GL (Fin B.rank) D.host.E) (u : GfC B),
      cT σ fr.1 * B.gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE B u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λs) ∧
      (∀ i (k : Fin A.rank), fr.1 i (Formalism.L2.Col.Br.iC d.rank.symm k) = (emb d * fr₀.1) i k) ∧
      (∀ i, fr.1 i (Formalism.L2.Col.Br.iL d.rank.symm) = d.a i 0) ∧
      HMul.hMul (mt B u.1) ((emb d).map (incA D)) = HMul.hMul ((emb d).map (incA D)) (mt A u₀.1) ∧
      mt B u.1 *ᵥ (fun i => incA D (d.a i 0)) = fun i => incA D (d.a i 0) := by
  obtain ⟨g, hg⟩ := exists_pt d u₀.1
  have m3 : (prj d).map (incA D) * (emb d).map (incA D) = 1 := by
    rw [← Matrix.map_mul, prj_emb, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgf : g ∈ GfC B := by
    have h0 : ((matHom A u₀.1).1).map (rhoI D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 u₀.2)
    refine MonoidHom.mem_ker.2 (Units.ext ?_)
    show (infHom B g).1 = 1
    rw [infHom_val, hg, extM_map, h0, extM_one]
  have hfin : (Formalism.IndefR.Lev.finE B g).1 = extM ((emb d).map (inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))
      ((prj d).map (inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) (Formalism.IndefR.Lev.finE A u₀.1).1 := by
    rw [finE_val, finE_val, hg, extM_map, map_incA_rhoF, map_incA_rhoF]
  refine ⟨frG d fr₀.1 hon, ⟨g, hgf⟩, frM_on d _ hon, ?_, fun v => ?_, frM_iC d _, frM_iL d _, ?_, ?_⟩
  · obtain ⟨P, e, he, hs, ho⟩ := hsu
    refine ⟨P, e, he, fun i j => ?_, ho⟩
    exact (congrArg (fun X => (e + cA D e) * (X - 1) i j) hg).trans
      ((extM_supp _ _ _ _ hs i j).trans (congrArg (fun X => (X - 1) i j) hg.symm))
  · subst hΛ
    rw [colLat_frG d fr₀ hon]
    show _ ↔ (Formalism.IndefR.Lev.finE B g).1 *ᵥ v ∈ _
    rw [hfin]
    exact hat_transport (prj_emb d) (orthogonalSumProjection_mul_auxiliary d) (crd_emb d) (coefficient_mul_a_eq_one d) (split_map _ d) (mem_lat d _) (mem_lat d _) _ hl v
  · exact Eq.trans (congrArg (fun X : Matrix (Fin B.rank) (Fin B.rank) (AF D.host.F ⊗[D.host.F] D.host.E) =>
      HMul.hMul X ((emb d).map (incA D))) hg) (extM_mul _ _ _ m3)
  · have hq : (prj d).map (incA D) *ᵥ (fun i => incA D (d.a i 0)) = 0 := by
      funext l
      have := congrArg (incA D) (congrFun (congrFun (orthogonalSumProjection_mul_auxiliary d) l) 0)
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, map_sum] using this
    exact Eq.trans (congrArg (fun X : Matrix (Fin B.rank) (Fin B.rank) (AF D.host.F ⊗[D.host.F] D.host.E) =>
      X *ᵥ (fun i => incA D (d.a i 0))) hg) (extM_mulVec _ _ _ hq)

end GlobalTheory.TopExt

namespace GlobalTheory.FunObj

theorem top_transport : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (S : Finset ℕ)
    (fr₀ : GL (Fin (G.V (.grid D.R.m D.R.m)).rank) D.host.E) (u₀ : FinPt G (.grid D.R.m D.R.m)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr₀.1 * (G.V (.grid D.R.m D.R.m)).gram * fr₀.1 = 1 →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u₀.1 ∧ ∀ w ∈ P, Off S w) →
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr₀) ↔
        (Formalism.IndefR.Lev.finE (G.V (.grid D.R.m D.R.m)) u₀.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid D.R.m D.R.m))) →
    ∃ (fr : GL (Fin (G.V (.top D.R.m)).rank) D.host.E) (u : FinPt G (.top D.R.m)),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * (G.V (.top D.R.m)).gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE (G.V (.top D.R.m)) u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top D.R.m))) ∧
      (∀ i (k : Fin (G.V (.grid D.R.m D.R.m)).rank), fr.1 i (Formalism.L2.Col.Br.iC G.sp.topDec.rank.symm k) =
        (frameMat _ _ G.sp.topDec.ι * fr₀.1) i k) ∧
      (∀ i, fr.1 i (Formalism.L2.Col.Br.iL G.sp.topDec.rank.symm) = G.sp.topDec.a i 0) ∧
      HMul.hMul (mt (G.V (.top D.R.m)) u.1) (topEmb G) = HMul.hMul (topEmb G) (mt (G.V (.grid D.R.m D.R.m)) u₀.1) ∧
      mt (G.V (.top D.R.m)) u.1 *ᵥ topVec G = topVec G := by
  intro D T L sc G S fr₀ u₀ hon hs hl
  exact GlobalTheory.TopExt.top_abs (A := G.V (.grid D.R.m D.R.m)) (B := G.V (.top D.R.m))
    G.sp.topDec S (G.Λ (.grid D.R.m D.R.m)) (G.Λ (.top D.R.m)) G.sp.topLat fr₀ u₀ hon hs hl

end GlobalTheory.FunObj

end
