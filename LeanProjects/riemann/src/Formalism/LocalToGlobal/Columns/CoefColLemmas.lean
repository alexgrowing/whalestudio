import Mathlib
import Formalism.LocalToGlobal.Columns.CoefCol
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.LocalToGlobal.Columns.BaseLemmas

open NumberField IsDedekindDomain Module
open scoped Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section GLmat

variable {E : Type} [Field E] {n : ℕ}

theorem toGLm_mulVec (ga : Sp E n ≃ₗ[E] Sp E n) (x : Sp E n) :
    ((toGLm E n ga : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x = ga x := by
  have h : Matrix.GeneralLinearGroup.toLin (toGLm E n ga) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv E (Sp E n)).symm ga := by
    simp [toGLm]
  have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup E (Sp E n) => (u : Sp E n →ₗ[E] Sp E n) x) h
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply] at h2
  rw [h2]
  rfl

theorem gmap_eq_map (ga : Sp E n ≃ₗ[E] Sp E n) {R : Type} [CommRing R] [Algebra R E]
    (L : Submodule R (Sp E n)) :
    gmap ga L = L.map ((Matrix.mulVecLin ((toGLm E n ga : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).restrictScalars R) := by
  ext x
  simp [gmap, toGLm_mulVec]

end GLmat

section DecoAct

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem Deco.L_act (d : Deco E n ST SG) (ga : Sp E n ≃ₗ[E] Sp E n) (h : GLG E n SG) :
    (d.act ga h).L = gmap ga d.L := by
  unfold Deco.L gmap
  rw [Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Deco.act, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨hx, hf⟩
    refine ⟨ga.symm x, ⟨(mem_gmap ga d.N x).1 hx, hf⟩, by simp⟩
  · rintro ⟨y, ⟨hy, hf⟩, rfl⟩
    refine ⟨(mem_gmap ga d.N (ga y)).2 (by simpa using hy), fun P => by simpa using hf P⟩

theorem Deco.Lsh_act (d : Deco E n ST SG) {ga : Sp E n ≃ₗ[E] Sp E n} (hga : ga ∈ UF E n) (h : GLG E n SG) :
    (d.act ga h).Lsh = gmap ga d.Lsh := by
  unfold Deco.Lsh
  rw [Deco.L_act, dual_gmap ga hga]

theorem Deco.LshKer_act (d : Deco E n ST SG) {ga : Sp E n ≃ₗ[E] Sp E n} (hga : ga ∈ UF E n)
    (h : GLG E n SG) (P : ST) :
    (d.act ga h).LshKer P = gmap ga (d.LshKer P) := by
  unfold Deco.LshKer gmap
  rw [Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  rw [Deco.Lsh_act d hga h]
  constructor
  · rintro ⟨hx, hf⟩
    refine ⟨ga.symm x, ⟨(mem_gmap ga d.Lsh x).1 hx, hf⟩, by simp⟩
  · rintro ⟨y, ⟨hy, hf⟩, rfl⟩
    refine ⟨(mem_gmap ga d.Lsh (ga y)).2 (by simpa using hy), by simpa [Deco.act] using hf⟩

theorem Deco.N_act (d : Deco E n ST SG) (ga : Sp E n ≃ₗ[E] Sp E n) (h : GLG E n SG) :
    (d.act ga h).N = gmap ga d.N := rfl

end DecoAct

section KLat

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem mem_dualFr (M : Submodule (𝓞 K) (Fin n → K)) (φ : Fin n → K) :
    φ ∈ dualFr M ↔ ∀ x ∈ M, φ ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K) := Iff.rfl

theorem mem_gLat (g : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) (x : Fin n → K) :
    x ∈ gLat g M ↔ ∃ y ∈ M, (g : Matrix (Fin n) (Fin n) K) *ᵥ y = x := by
  simp [gLat]

theorem dualFr_gLat (g : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) :
    dualFr (gLat g M) = gLat (inside₂ K n g) (dualFr M) := by
  have hinv : (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ * (g : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  ext φ
  rw [mem_dualFr, mem_gLat]
  constructor
  · intro h
    refine ⟨(g : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ φ, ?_, ?_⟩
    · intro x hx
      have := h ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ((mem_gLat g M _).2 ⟨x, hx, rfl⟩)
      rwa [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at this
    · show (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ *ᵥ ((g : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ φ) = φ
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  · rintro ⟨ψ, hψ, rfl⟩ y hy
    obtain ⟨x, hx, rfl⟩ := (mem_gLat g M y).1 hy
    have := (mem_dualFr M ψ).1 hψ x hx
    show (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ *ᵥ ψ ⬝ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ∈ _
    rwa [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Units.inv_mul,
      Matrix.vecMul_one]

variable {ι : Type} [Fintype ι]

theorem nabK_gLat (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K) :
    nabK lam (fun τ => gLat (g τ) (M τ)) = (nabK lam M).map ((rhoK lam g).restrictScalars (𝓞 K)) := by
  have hE := (nabDelEquiv K ι n lam M g).1
  ext x
  simp only [nabK, Submodule.mem_comap, Submodule.mem_map,
    LinearMap.coe_restrictScalars, Submodule.subtype_apply]
  rw [hE, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyV : y ∈ VV K lam := by
      have : y = actP lam g⁻¹ x.1 := by
        rw [← hyx]
        show y = actP lam g⁻¹ (actP lam g y)
        rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
      rw [this]
      exact polyAction_mem_VV lam g⁻¹ x.2
    exact ⟨⟨y, hyV⟩, hy, Subtype.ext (by rw [rhoK_coe]; exact hyx)⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, hy, (rhoK_coe lam g y).symm⟩

theorem delK_gLat (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K) :
    delK lam (fun τ => gLat (g τ) (M τ)) = (delK lam M).map ((rhoK lam g).restrictScalars (𝓞 K)) := by
  have hE := (nabDelEquiv K ι n lam M g).2
  ext x
  simp only [delK, Submodule.mem_comap, Submodule.mem_map,
    LinearMap.coe_restrictScalars, Submodule.subtype_apply]
  rw [hE, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyV : y ∈ VV K lam := by
      have : y = actP lam g⁻¹ x.1 := by
        rw [← hyx]
        show y = actP lam g⁻¹ (actP lam g y)
        rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
      rw [this]
      exact polyAction_mem_VV lam g⁻¹ x.2
    exact ⟨⟨y, hyV⟩, hy, Subtype.ext (by rw [rhoK_coe]; exact hyx)⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, hy, (rhoK_coe lam g y).symm⟩

end KLat

section Brackets

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K)

theorem tauLat_gmap (τ : ι) (ga : Sp E n ≃ₗ[E] Sp E n) (L : Submodule (𝓞 E) (Sp E n)) :
    tauLat emb τ (gmap ga L) = gLat (embGL emb (toGLm E n ga) τ) (tauLat emb τ L) := by
  rw [gmap_eq_map]
  exact tauLatG E K ι n emb τ L (toGLm E n ga)

theorem nabAt_gmap (lam : ι → DomWeight n) (ga : Sp E n ≃ₗ[E] Sp E n) (L : Submodule (𝓞 E) (Sp E n)) :
    nabAt emb lam (gmap ga L) = (nabAt emb lam L).map ((rhoV emb lam (toGLm E n ga)).restrictScalars (𝓞 K)) := by
  unfold nabAt
  simp_rw [tauLat_gmap]
  exact nabK_gLat lam _ _

theorem delAt_gmap (lam : ι → DomWeight n) (ga : Sp E n ≃ₗ[E] Sp E n) (L : Submodule (𝓞 E) (Sp E n)) :
    delAt emb lam (gmap ga L) = (delAt emb lam L).map ((rhoV emb lam (toGLm E n ga)).restrictScalars (𝓞 K)) := by
  unfold delAt
  simp_rw [tauLat_gmap]
  exact delK_gLat lam _ _

theorem nabAtr_gmap (lam : ι → DomWeight n) (ga : Sp E n ≃ₗ[E] Sp E n) (L : Submodule (𝓞 E) (Sp E n)) :
    nabAtr emb lam (gmap ga L) = (nabAtr emb lam L).map ((rhoVr emb lam (toGLm E n ga)).restrictScalars (𝓞 K)) := by
  unfold nabAtr
  simp_rw [tauLat_gmap, dualFr_gLat]
  exact nabK_gLat lam _ (invTrK (embGL emb (toGLm E n ga)))

theorem delAtr_gmap (lam : ι → DomWeight n) (ga : Sp E n ≃ₗ[E] Sp E n) (L : Submodule (𝓞 E) (Sp E n)) :
    delAtr emb lam (gmap ga L) = (delAtr emb lam L).map ((rhoVr emb lam (toGLm E n ga)).restrictScalars (𝓞 K)) := by
  unfold delAtr
  simp_rw [tauLat_gmap, dualFr_gLat]
  exact delK_gLat lam _ (invTrK (embGL emb (toGLm E n ga)))

end Brackets

section PkEquiv

variable (X : Fields) {n : ℕ} (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n))

theorem roundPk_nab {ga : UF X.E n} {d d' : D} (h : L d' = gmap ga.1 (L d)) :
    (roundPk X lam L).Nab d' = ((roundPk X lam L).Nab d).map (((roundPk X lam L).rho ga).restrictScalars (𝓞 X.K)) := by
  show nabAtr X.emb lam (L d') = _
  rw [h, nabAtr_gmap]
  rfl

theorem roundPk_del {ga : UF X.E n} {d d' : D} (h : L d' = gmap ga.1 (L d)) :
    (roundPk X lam L).Del d' = ((roundPk X lam L).Del d).map (((roundPk X lam L).rho ga).restrictScalars (𝓞 X.K)) := by
  show delAtr X.emb lam (L d') = _
  rw [h, delAtr_gmap]
  rfl

theorem squarePk_nab {ga : UF X.E n} {d d' : D} (h : L d' = gmap ga.1 (L d)) :
    (squarePk X lam L).Nab d' = ((squarePk X lam L).Nab d).map (((squarePk X lam L).rho ga).restrictScalars (𝓞 X.K)) := by
  show nabAt X.emb lam (L d') = _
  rw [h, nabAt_gmap]
  rfl

theorem squarePk_del {ga : UF X.E n} {d d' : D} (h : L d' = gmap ga.1 (L d)) :
    (squarePk X lam L).Del d' = ((squarePk X lam L).Del d).map (((squarePk X lam L).rho ga).restrictScalars (𝓞 X.K)) := by
  show delAt X.emb lam (L d') = _
  rw [h, delAt_gmap]
  rfl

end PkEquiv

section ValsEquiv

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem colVal_nab_smul (u : Pr.Word) (j : ℕ) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (a : UF X.E (R.N j) × GLG X.E (R.N j) SG) (d : DecoSet X.E (R.N j) ST SG) :
    (colVal W u j ST SG).Nab (a • d) =
      ((colVal W u j ST SG).Nab d).map (((colVal W u j ST SG).rho a.1).restrictScalars (𝓞 X.K)) :=
  roundPk_nab X _ _ (d.1.Lsh_act a.1.2 a.2)

theorem colVal_del_smul (u : Pr.Word) (j : ℕ) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (a : UF X.E (R.N j) × GLG X.E (R.N j) SG) (d : DecoSet X.E (R.N j) ST SG) :
    (colVal W u j ST SG).Del (a • d) =
      ((colVal W u j ST SG).Del d).map (((colVal W u j ST SG).rho a.1).restrictScalars (𝓞 X.K)) :=
  roundPk_del X _ _ (d.1.Lsh_act a.1.2 a.2)

theorem BvLat_smul (u : Pr.Word) (j : ℕ) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST)
    (a : UF X.E (R.N j) × GLG X.E (R.N j) SG) (d : DecoSet X.E (R.N j) ST SG) :
    BvLat W u j P (a • d) = (BvLat W u j P d).map (((colVal W u j ST SG).rho a.1).restrictScalars (𝓞 X.K)) := by
  show delAtr X.emb (W.lamTrue u j) ((a • d).1.LshKer P) = _
  rw [DecoSet.smul_val, Deco.LshKer_act _ a.1.2, delAtr_gmap]
  rfl

theorem rowVal_nab_smul {SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (a : UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) SG) (d : DecoSet X.E (R.N R.m - 1) ∅ SG) :
    (rowVal W SG).Nab (a • d) = ((rowVal W SG).Nab d).map (((rowVal W SG).rho a.1).restrictScalars (𝓞 X.K)) :=
  squarePk_nab X _ _ (d.1.N_act a.1.1 a.2)

theorem rowVal_del_smul {SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (a : UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) SG) (d : DecoSet X.E (R.N R.m - 1) ∅ SG) :
    (rowVal W SG).Del (a • d) = ((rowVal W SG).Del d).map (((rowVal W SG).rho a.1).restrictScalars (𝓞 X.K)) :=
  squarePk_del X _ _ (d.1.N_act a.1.1 a.2)

theorem mtVal_nab_smul (j : ℕ) {SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (a : UF X.E R.nV × GLG X.E R.nV SG) (d : DecoSet X.E R.nV ∅ SG) :
    (mtVal W j SG).Nab (a • d) = ((mtVal W j SG).Nab d).map (((mtVal W j SG).rho a.1).restrictScalars (𝓞 X.K)) :=
  roundPk_nab X _ _ (d.1.N_act a.1.1 a.2)

theorem mtVal_del_smul (j : ℕ) {SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (a : UF X.E R.nV × GLG X.E R.nV SG) (d : DecoSet X.E R.nV ∅ SG) :
    (mtVal W j SG).Del (a • d) = ((mtVal W j SG).Del d).map (((mtVal W j SG).rho a.1).restrictScalars (𝓞 X.K)) :=
  roundPk_del X _ _ (d.1.N_act a.1.1 a.2)

end ValsEquiv

section PkPair

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem glEquiv_toGLm (ga : Sp E n ≃ₗ[E] Sp E n) : Formalism.UG.glEquiv (toGLm E n ga) = ga := by
  ext x
  rw [Formalism.UG.P.glEquiv_apply', toGLm_mulVec]

theorem gram_hStd : Formalism.UG.gram (hStd E n) = 1 := by
  ext i j
  change (∑ k, star ((Pi.single i (1 : E) : Sp E n) k) * (Pi.single j (1 : E) : Sp E n) k) = (1 : Matrix (Fin n) (Fin n) E) i j
  rw [Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp [Pi.single_apply]
  · simp [Pi.single_apply, h, Ne.symm h]

theorem toGLm_mem_UJ (ga : UF E n) : toGLm E n ga.1 ∈ Formalism.UG.UJ (starRingEnd E) (1 : Matrix (Fin n) (Fin n) E) := by
  have h := (Formalism.UG.P.hermitian_lattice_correspondence_holds E (Fin n) (hStd E n) (toGLm E n ga.1)).2
  rw [gram_hStd, glEquiv_toGLm] at h
  exact h ga.2

end PkPair

section PkPair2

variable (X : Fields) {n : ℕ} (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n))

theorem roundPk_inv (hst : ∀ (τ : X.Tau) (x : X.E), X.emb τ (star x) = star (X.emb τ x)) (ga : UF X.E n)
    (x y : VV X.K lam) :
    (roundPk X lam L).pair ((roundPk X lam L).rho ga x) ((roundPk X lam L).rho ga y) = (roundPk X lam L).pair x y :=
  pairInv X.K X.Tau n lam _ _ (fun τ => (uJUnitary X.E X.K X.Tau n X.emb (starRingEnd X.E) τ
    (fun x => (hst τ x).symm) 1 _ (toGLm_mem_UJ ga)).2 (by simp)) x y

theorem squarePk_inv (hst : ∀ (τ : X.Tau) (x : X.E), X.emb τ (star x) = star (X.emb τ x)) (ga : UF X.E n)
    (x y : VV X.K lam) :
    (squarePk X lam L).pair ((squarePk X lam L).rho ga x) ((squarePk X lam L).rho ga y) = (squarePk X lam L).pair x y :=
  pairInv X.K X.Tau n lam _ _ (fun τ => (uJUnitary X.E X.K X.Tau n X.emb (starRingEnd X.E) τ
    (fun x => (hst τ x).symm) 1 _ (toGLm_mem_UJ ga)).1) x y

theorem roundPk_del_le (d : D) : (roundPk X lam L).Del d ≤ (roundPk X lam L).Nab d :=
  delLeNab X.K X.Tau n lam _

theorem squarePk_del_le (d : D) : (squarePk X lam L).Del d ≤ (squarePk X lam L).Nab d :=
  delLeNab X.K X.Tau n lam _

end PkPair2

section NonVac

variable (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ}

def extVV (lam : ι → DomWeight n) : Pol K ι n := ten fun τ => extremal K n (lam τ)

theorem extVV_mem (lam : ι → DomWeight n) : extVV K lam ∈ VV K lam :=
  Submodule.subset_span ⟨fun τ => extremal K n (lam τ),
    fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (natW_antitone (lam τ)), rfl⟩

theorem extVV_ne_zero (lam : ι → DomWeight n) : extVV K lam ≠ 0 := by
  unfold extVV ten
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  have hinj : Function.Injective (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ) :=
    MvPolynomial.rename_injective _ (fun a b h => (Prod.mk.inj h).2)
  exact (map_ne_zero_iff _ hinj).mpr (Formalism.GradedWeylDivisibility.hwNe K n n le_rfl _)

instance VV_nontrivial (lam : ι → DomWeight n) : Nontrivial (VV K lam) :=
  ⟨⟨⟨extVV K lam, extVV_mem K lam⟩, 0, fun h => extVV_ne_zero K lam (congrArg Subtype.val h)⟩⟩

theorem CoefPk.V_nontrivial {X : Fields} {D : Type} (C : CoefPk X n D) : Nontrivial C.V := VV_nontrivial X.K C.lam

theorem CoefPk.finrank_pos {X : Fields} {D : Type} (C : CoefPk X n D) : 0 < Module.finrank X.K C.V := by
  have := C.V_nontrivial
  have : Module.Finite X.K C.V := Module.Finite.of_basis C.bV
  exact Module.finrank_pos

end NonVac

section LastEntry

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

theorem lamTrue_sgTrue_detShift (hW : W.Ok) (u : Word) (τ : X.Tau) :
    (W.lamTrue u R.m τ).detShift = (W.sgTrue τ).detShift := by
  have hm := R.two_le_m
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  have ht : 1 ≤ R.t := R.t_odd.pos
  have hmul : R.m * (R.t + 1) = (R.m - 1) * (R.t + 1) + (R.t + 1) := by
    rw [← Nat.succ_mul]; congr 1; omega
  have hN : R.N R.m = R.k + (R.m - 1) * (R.t + 1) + R.t + 1 := by unfold Ranks.N; rw [hmul]; ring
  have hN1 : 0 < R.N R.m := by omega
  have hN2 : 0 < R.N R.m - 1 := by omega
  unfold DomWeight.detShift
  rw [dif_pos hN1, dif_pos hN2]
  apply Int.cast_injective (α := ℚ)

  rw [Wts.lamTrue_eq, Wts.lamN_eq W u le_rfl]
  have hlt : ¬ R.N R.m - 1 < R.k := by omega
  rw [dif_neg hlt]
  have e1 : (R.N R.m - 1 - R.k) / (R.t + 1) = R.m - 1 := by
    have : R.N R.m - 1 - R.k = (R.m - 1) * (R.t + 1) + R.t := by omega
    rw [this]
    exact (divmod (R.t + 1) (R.m - 1) R.t (by omega)).1
  simp only [e1]

  obtain ⟨P, hP⟩ := hW.row_ok τ
  have hrow : (W.hc u τ).e = P.e := by
    have := congrArg RowPar.e ((hW.hc_row u τ).trans hP.symm)
    simpa [RowPar.of] using this
  rw [hrow]
  show _ = (((W.row τ).sgTrue.w ⟨R.N R.m - 1 - 1, by omega⟩ : ℤ) : ℚ)
  rw [← hP, RowPar.sgTrue_eq]
  have hi : R.N R.m - 1 - 1 = R.k - 1 + (R.m - 1) * (R.t + 1) + R.t := by omega
  simp only [hi]
  rw [RowPar.sgHC_e _ (R.m - 1) R.t ht le_rfl, RowPar.eAt_of P (by omega)]
  unfold rhoVec wG RowPar.sh
  have c1 : ((R.N R.m - 1 : ℕ) : ℚ) = (R.k : ℚ) + ((R.m : ℚ) - 1) * ((R.t : ℚ) + 1) + R.t := by
    rw [hN]; push_cast [Nat.cast_sub (by omega : 1 ≤ R.m)]; ring
  have c2 : ((R.k - 1 + (R.m - 1) * (R.t + 1) + R.t : ℕ) : ℚ) = (R.k : ℚ) - 1 + ((R.m : ℚ) - 1) * ((R.t : ℚ) + 1) + R.t := by
    push_cast [Nat.cast_sub hk, Nat.cast_sub (by omega : 1 ≤ R.m)]; ring
  rw [c1, c2]
  push_cast [Nat.cast_sub (by omega : 1 ≤ R.m)]
  ring

end LastEntry

end Formalism.L2.Col
