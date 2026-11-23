import Formalism.LocalToGlobal.GlobalTheory.GL6.PRUpLoc
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrLoc

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section LocGen

theorem rlv_mem_locP {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (P : Ideal R) [P.IsPrime]
    (L : Submodule R W) (x : W) : x ∈ Formalism.HermitianLatticesTheory.localization₂ P L ↔ ∃ s : R, s ∉ P ∧ s • x ∈ L :=
  ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩⟩

theorem rlv_two {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    {L M : Submodule R W} (hP : Formalism.HermitianLatticesTheory.localization₂ P L ≤ Formalism.HermitianLatticesTheory.localization₂ P M)
    (hQ : Formalism.HermitianLatticesTheory.localization₂ Q L ≤ Formalism.HermitianLatticesTheory.localization₂ Q M) {x : W} (hx : x ∈ L) :
    ∃ a : R, a ∉ P ∧ a ∉ Q ∧ a • x ∈ M := by
  obtain ⟨s, hs, hsx⟩ := (rlv_mem_locP P M x).1 (hP ((rlv_mem_locP P L x).2 ⟨1, P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance), by rw [one_smul]; exact hx⟩))
  obtain ⟨t, ht, htx⟩ := (rlv_mem_locP Q M x).1 (hQ ((rlv_mem_locP Q L x).2 ⟨1, Q.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance), by rw [one_smul]; exact hx⟩))
  by_cases hsQ : s ∈ Q
  · by_cases htP : t ∈ P
    · refine ⟨s + t, fun h => hs ?_, fun h => ht ?_, ?_⟩
      · simpa using P.sub_mem h htP
      · simpa using Q.sub_mem h hsQ
      · rw [add_smul]; exact M.add_mem hsx htx
    · exact ⟨t, htP, ht, htx⟩
  · exact ⟨s, hs, hsQ, hsx⟩

end LocGen

section LatS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem rlv_unit (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    ∃ s ∈ intV E v, s * ((1 : E) ⊗ₜ[F] (algebraMap F (v.adicCompletion F) (r : F))) = 1 := by
  have hu : IsUnit (algebraMap (𝓞 F) (v.adicCompletionIntegers F) r) := by
    rw [← IsLocalRing.notMem_maximalIdeal, mem_maximal_ideal_completion_iff]; exact hr
  obtain ⟨w, hw⟩ := hu.exists_left_inv
  refine ⟨(1 : E) ⊗ₜ[F] ((w : v.adicCompletion F)), Subring.subset_closure (Or.inr ⟨w, rfl⟩), ?_⟩
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have h1 : ((w : v.adicCompletionIntegers F) : v.adicCompletion F) * (algebraMap F (v.adicCompletion F) (r : F)) = 1 := by
    have := congrArg (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) hw
    exact this
  rw [h1]; rfl

theorem rlv_incl_smul (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (y : E) :
    inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) r) • y) =
      inclE (F := F) (v.adicCompletion F) y * ((1 : E) ⊗ₜ[F] (algebraMap F (v.adicCompletion F) (r : F))) := by
  have e1 : (algebraMap (𝓞 F) (𝓞 E) r) • y = (r : F) • y := by
    rw [Algebra.smul_def, Algebra.smul_def]; rfl
  rw [e1]
  show ((r : F) • y) ⊗ₜ[F] (1 : v.adicCompletion F) = (y ⊗ₜ[F] (1 : v.adicCompletion F)) * _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem rlv_latS_mono (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
    {L M : Submodule (𝓞 E) (n → E)}
    (h : ∀ x ∈ L, ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ (algebraMap (𝓞 F) (𝓞 E) r) • x ∈ M) :
    latS (F := F) (v.adicCompletion F) (intV E v) L ≤ latS (F := F) (v.adicCompletion F) (intV E v) M := by
  apply Submodule.span_le.2
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hrx⟩ := h x hx
  obtain ⟨s, hs, hsr⟩ := rlv_unit (E := E) v r hr
  have hm : (fun i => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) r) • x) i)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) M :=
    Submodule.subset_span ⟨_, hrx, rfl⟩
  have h2 := (latS (F := F) (v.adicCompletion F) (intV E v) M).smul_mem ⟨s, hs⟩ hm
  have e : (fun i => inclE (F := F) (v.adicCompletion F) (x i)) = (⟨s, hs⟩ : intV E v) •
      (fun i => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) r) • x) i)) := by
    funext i
    show inclE (F := F) (v.adicCompletion F) (x i) = s * inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) r) • x) i)
    rw [Pi.smul_apply, rlv_incl_smul]
    calc inclE (F := F) (v.adicCompletion F) (x i) = inclE (F := F) (v.adicCompletion F) (x i) * 1 := (mul_one _).symm
      _ = _ := by rw [← hsr]; ring
  show (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ (latS (F := F) (v.adicCompletion F) (intV E v) M : Set _)
  rw [e]; exact h2

theorem rlv_latS_mulLat {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (γ : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E ⊗[F] v.adicCompletion F)
    (hx : x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L) :
    (γ.map (inclE (F := F) (v.adicCompletion F))) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (mulLat γ L) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y, hy, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨γ *ᵥ y, ⟨y, hy, rfl⟩, ?_⟩
    funext i
    exact RingHom.map_mulVec _ _ _ _
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul a b _ hb =>
    have e : (γ.map (inclE (F := F) (v.adicCompletion F))) *ᵥ (a • b) = a • ((γ.map (inclE (F := F) (v.adicCompletion F))) *ᵥ b) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show _ * ((a : E ⊗[F] v.adicCompletion F) * b j) = (a : E ⊗[F] v.adicCompletion F) * (_ * b j)
      ring
    rw [e]; exact Submodule.smul_mem _ a hb

end LatS

section LatS2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem rlv_locV (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n] (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime]
    (hN : ∀ a : 𝓞 E, a ∉ P → a ∉ Q → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ ∃ b : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) r = b * a)
    {L M : Submodule (𝓞 E) (n → E)} (hP : Formalism.HermitianLatticesTheory.localization₂ P L ≤ Formalism.HermitianLatticesTheory.localization₂ P M)
    (hQ : Formalism.HermitianLatticesTheory.localization₂ Q L ≤ Formalism.HermitianLatticesTheory.localization₂ Q M) :
    latS (F := F) (v.adicCompletion F) (intV E v) L ≤ latS (F := F) (v.adicCompletion F) (intV E v) M := by
  apply rlv_latS_mono
  intro x hx
  obtain ⟨a, haP, haQ, hax⟩ := rlv_two P Q hP hQ hx
  obtain ⟨r, hr, b, hb⟩ := hN a haP haQ
  refine ⟨r, hr, ?_⟩
  rw [hb, mul_smul]
  exact M.smul_mem b hax

theorem rlv_map_inv_mul {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (φ : A →+* B) (g : GL n A)
    (w : n → B) : ((g⁻¹ : GL n A) : Matrix n n A).map φ *ᵥ ((g : Matrix n n A).map φ *ᵥ w) = w := by
  rw [mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one φ φ.map_zero φ.map_one, one_mulVec]

theorem rlv_mulLat_inv {n : ℕ} (g : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    mulLat ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) (mulLat (g : Matrix (Fin n) (Fin n) E) L) = L := by
  ext x
  simp only [mulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rwa [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  · intro hx
    exact ⟨(g : Matrix (Fin n) (Fin n) E) *ᵥ x, ⟨x, hx, rfl⟩, by
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]⟩

theorem rlv_yloc (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n] {L Lb : Submodule (𝓞 E) (n → E)}
    (y : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F L ↔ ((y⁻¹ : GL n _) : Matrix n n _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lb)
    (x : n → E ⊗[F] v.adicCompletion F) :
    x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      ((bc (prV (E := E) v) y⁻¹ : GL n _) : Matrix n n _) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb := by
  constructor
  · intro hx
    exact Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.loc_fwd v y⁻¹ (fun u hu => (hy u).1 hu) x hx
  · intro hx
    have h1 : ∀ u ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lb, (y : Matrix n n _) *ᵥ u ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F L := by
      intro u hu
      apply (hy _).2
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      exact hu
    have h2 := Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.loc_fwd v y h1 _ hx
    rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec] at h2

theorem rlv_stab {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {Lb L1 L2 : Submodule (𝓞 E) (Fin n → E)}
    (y1 y2 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy1 : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F L1 ↔ ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lb)
    (hy2 : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F L2 ↔ ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lb)
    (g : GL (Fin n) E)
    (hle : latS (F := F) (v.adicCompletion F) (intV E v) (mulLat (g : Matrix (Fin n) (Fin n) E) L2) ≤
      latS (F := F) (v.adicCompletion F) (intV E v) L1)
    (hge : latS (F := F) (v.adicCompletion F) (intV E v) L1 ≤
      latS (F := F) (v.adicCompletion F) (intV E v) (mulLat (g : Matrix (Fin n) (Fin n) E) L2)) :
    bc (prV (E := E) v) (y1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g * y2) ∈
      stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb) := by
  intro x
  have hG : ((bc (prV (E := E) v) (y1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g * y2) : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _) *ᵥ x = ((bc (prV (E := E) v) y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (((g : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F))) *ᵥ
          (((bc (prV (E := E) v) y2 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x)) := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    rfl
  rw [hG]
  have hY2 : ∀ w, w ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb ↔
      ((bc (prV (E := E) v) y2 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ w ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 := by
    intro w
    rw [rlv_yloc v y2 hy2, mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  constructor
  · intro hx
    refine (rlv_yloc v y1 hy1 _).1 (hle ?_)
    exact rlv_latS_mulLat v _ L2 _ ((hY2 x).1 hx)
  · intro hx
    have h1 := (rlv_yloc v y1 hy1 _).2 hx
    have h2 := rlv_latS_mulLat v ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) _ _ (hge h1)
    rw [rlv_mulLat_inv, rlv_map_inv_mul] at h2
    exact (hY2 x).2 h2

end LatS2

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem rlv_mem_U (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (η η' : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hη : ∀ v', v' ≠ v → bc (prV (E := E) v') η.1 = 1) (hη' : ∀ v', v' ≠ v → bc (prV (E := E) v') η'.1 = 1)
    (κ κ' : S.U) (hv : bc (prV (E := E) v) (η.1 * κ.1 * η'.1 * κ'.1) ∈ S.Uloc v) :
    η.1 * κ.1 * η'.1 * κ'.1 ∈ S.U := by
  have hκ := (S.U_eq _).1 κ.2
  have hκ' := (S.U_eq _).1 κ'.2
  rw [S.U_eq]
  refine ⟨mul_mem (mul_mem (mul_mem η.2 hκ.1) η'.2) hκ'.1, fun v' => ?_⟩
  by_cases h : v' = v
  · subst h; exact hv
  · rw [map_mul, map_mul, map_mul, hη v' h, hη' v' h, one_mul, mul_one]
    exact mul_mem (hκ.2 v') (hκ'.2 v')

theorem rlv_comp_eq {G : Type} [Group G] (y y' y'' η κ η' κ' g g' : G)
    (h1 : g * y' = y * η * κ) (h2 : g' * y'' = y' * η' * κ') :
    η * κ * η' * κ' = y⁻¹ * (g * g') * y'' := by
  have e1 : η * κ = y⁻¹ * g * y' := by rw [mul_assoc y⁻¹, h1]; group
  have e2 : η' * κ' = y'⁻¹ * g' * y'' := by rw [mul_assoc y'⁻¹, h2]; group
  calc η * κ * η' * κ' = (η * κ) * (η' * κ') := by group
    _ = _ := by rw [e1, e2]; group

end Lev

section Chain

variable {E : Type} [Field E] [NumberField E]

theorem rlv_mulLat_mul {n : ℕ} (g g' : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    mulLat (g * g') L = mulLat g (mulLat g' L) := by
  ext x
  simp only [mulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g' *ᵥ y, ⟨y, hy, rfl⟩, by rw [mulVec_mulVec]⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by rw [mulVec_mulVec]⟩

theorem rlv_locP_mulLat_le {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime] (g : Matrix (Fin n) (Fin n) E)
    {M N : Submodule (𝓞 E) (Fin n → E)} (h : Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N) :
    Formalism.HermitianLatticesTheory.localization₂ P (mulLat g M) ≤ Formalism.HermitianLatticesTheory.localization₂ P (mulLat g N) := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (rlv_mem_locP _ _ _).1 hx
  obtain ⟨m, hm, hme⟩ := Submodule.mem_map.1 hsx
  obtain ⟨t, ht, htm⟩ := (rlv_mem_locP _ _ _).1 (h ((rlv_mem_locP _ _ _).2
    ⟨1, P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance), by rw [one_smul]; exact hm⟩))
  refine (rlv_mem_locP _ _ _).2 ⟨t * s, fun hts => (Ideal.IsPrime.mem_or_mem inferInstance hts).elim ht hs, ?_⟩
  refine Submodule.mem_map.2 ⟨t • m, htm, ?_⟩
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hme ⊢
  rw [Matrix.mulVec_smul, hme, mul_smul]

theorem rlv_chainP {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime] (g g' : Matrix (Fin n) (Fin n) E)
    {A B C : Submodule (𝓞 E) (Fin n → E)}
    (h1 : Formalism.HermitianLatticesTheory.localization₂ P (mulLat g A) = Formalism.HermitianLatticesTheory.localization₂ P B) (h2 : Formalism.HermitianLatticesTheory.localization₂ P (mulLat g' C) = Formalism.HermitianLatticesTheory.localization₂ P A) :
    Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g * g') C) = Formalism.HermitianLatticesTheory.localization₂ P B := by
  rw [rlv_mulLat_mul]
  exact le_antisymm ((rlv_locP_mulLat_le P g h2.le).trans h1.le) (h1.ge.trans (rlv_locP_mulLat_le P g h2.ge))

end Chain

section Tied

variable {D : D7} {u : D.what₂.Word}

def rlvQ (A : AtTTied u) (v : (D.mem u).A.vT) : Ideal (𝓞 D.host.E) :=
  (A.Pv v).comap (RingOfIntegers.mapRingHom (sigD D : D.host.E →+* D.host.E))

instance (A : AtTTied u) (v : (D.mem u).A.vT) : (rlvQ A v).IsPrime := Ideal.IsPrime.comap _

theorem rlv_norm (A : AtTTied u) (v : (D.mem u).A.vT) (a : 𝓞 D.host.E) (ha : a ∉ A.Pv v) (hq : a ∉ rlvQ A v) :
    ∃ r : 𝓞 D.host.F, r ∉ (A.eV v).1.asIdeal ∧ ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r = b * a := by
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 D.host.E, b = RingOfIntegers.mapRingHom (sigD D : D.host.E →+* D.host.E) a := ⟨_, rfl⟩
  have hbE : (b : D.host.E) = sigD D (a : D.host.E) := by rw [hb]; rfl
  have hσσ : ∀ x, sigD D (sigD D x) = x := fun x => by rw [forms_involution_eq_host_conj, forms_involution_eq_host_conj, host_conj_involutive]
  have hfix : ((b : D.host.E) * (a : D.host.E)) ∈ (algebraMap D.host.F D.host.E).range := by
    let _ := D.host.cmStar
    rw [← D.sp.cm.fixed]
    show sigD D ((b : D.host.E) * (a : D.host.E)) = (b : D.host.E) * (a : D.host.E)
    rw [map_mul, hbE, hσσ, mul_comm]
  obtain ⟨r0, hr0⟩ := hfix
  have hr0i : IsIntegral ℤ r0 := by
    have h1 : IsIntegral ℤ (algebraMap D.host.F D.host.E r0) := by
      rw [hr0]
      exact RingOfIntegers.isIntegral_coe (b * a)
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
      (algebraMap D.host.F D.host.E).injective).1 h1
  obtain ⟨r, hrr⟩ : ∃ r : 𝓞 D.host.F, (r : D.host.F) = r0 := ⟨⟨r0, hr0i⟩, rfl⟩
  have hr : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r = b * a := by
    apply RingOfIntegers.ext
    show algebraMap D.host.F D.host.E (r : D.host.F) = (b : D.host.E) * (a : D.host.E)
    rw [hrr, hr0]
  refine ⟨r, ?_, b, hr⟩
  have ha' : A.res v a ≠ 0 := fun h => ha (RingHom.mem_ker.2 h)
  have hb' : A.res v b ≠ 0 := by
    intro h
    apply hq
    show RingOfIntegers.mapRingHom (sigD D : D.host.E →+* D.host.E) a ∈ A.Pv v
    rw [← hb]
    exact RingHom.mem_ker.2 h
  rw [A.res_v v, hr, map_mul]
  exact mul_ne_zero hb' ha'

set_option synthInstance.maxHeartbeats 400000 in

theorem rlv_stabT (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c2 : (D.mem u).C.cls i)
    (g : GL (Fin (D.R.N i)) D.host.E)
    (hP : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (g : Matrix _ _ D.host.E) (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hQ : Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (mulLat (g : Matrix _ _ D.host.E) (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (clsCrd D u i hi c)) :
    bc (prV (E := D.host.E) (Tf.atT.eV v).1) (((Tf.cls i hi).y c).1⁻¹ *
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g * ((Tf.cls i hi).y c2).1) ∈
      stabGL (latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1) (Tf.cls i hi).lev.Lb) := by
  have hN := rlv_norm Tf.atT v
  exact rlv_stab (Tf.atT.eV v).1 ((Tf.cls i hi).y c).1 ((Tf.cls i hi).y c2).1 ((Tf.cls i hi).y_lat c) ((Tf.cls i hi).y_lat c2) g
    (rlv_locV (Tf.atT.eV v).1 (Tf.atT.Pv v) (rlvQ Tf.atT v) hN hP.le hQ.le)
    (rlv_locV (Tf.atT.eV v).1 (Tf.atT.Pv v) (rlvQ Tf.atT v) hN hP.ge hQ.ge)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem rlv_comp_mem (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c1 c2 : (D.mem u).C.cls i)
    (γ γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (η η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ κ' : (Tf.cls i hi).lev.U)
    (hsup : ∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1)
    (hsup' : ∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1)
    (hrel : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * ((Tf.cls i hi).y c1).1 =
      ((Tf.cls i hi).y c).1 * η.1 * κ.1)
    (hrel' : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 * ((Tf.cls i hi).y c2).1 =
      ((Tf.cls i hi).y c1).1 * η'.1 * κ'.1)
    (hP : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ.1 * γ'.1).1 (clsCrd D u i hi c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hQ : Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (mulLat (γ.1 * γ'.1).1 (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (clsCrd D u i hi c))
    (hF : bc (prV (E := D.host.E) (Tf.atT.eV v).1) (((Tf.cls i hi).y c).1⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ.1 * γ'.1) * ((Tf.cls i hi).y c2).1) ∈
      stabFun _ ((Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2)) :
    η.1 * κ.1 * η'.1 * κ'.1 ∈ (Tf.cls i hi).lev.U := by
  have hκ := ((Tf.cls i hi).lev.U_eq _).1 κ.2
  have hκ' := ((Tf.cls i hi).lev.U_eq _).1 κ'.2
  have hU : η.1 * κ.1 * η'.1 * κ'.1 ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    mul_mem (mul_mem (mul_mem η.2 hκ.1) η'.2) hκ'.1
  have heq := rlv_comp_eq ((Tf.cls i hi).y c).1 ((Tf.cls i hi).y c1).1 ((Tf.cls i hi).y c2).1 η.1 κ.1 η'.1 κ'.1
    (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1)
    (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1) hrel hrel'
  rw [← map_mul] at heq
  apply rlv_mem_U (Tf.cls i hi).lev (Tf.atT.eV v).1 η η' hsup hsup' κ κ'
  rw [(Tf.cls i hi).lev.UlocAlt _ (Tf.atT.eV v).2]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Formalism.UG.P.afsplit_bc_mem _ _ _ _ hU, ?_⟩, ?_⟩
  · have hs := rlv_stabT Tf i hi v c c2 (γ.1 * γ'.1) hP hQ
    rw [← heq] at hs
    exact hs
  · rw [heq]; exact hF

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def RUpLocV (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c ((Tf.lv i hi).pr v c z) = 1 →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = (D.fm u).fv i v c ((Tf.lv i hi).pr v c ⟨_, hx⟩)) →
    ∃ e : (D.fm u).lk i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lv i v c,
      e ((D.fm u).te i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) = (Tf.lv i hi).pr v c z ∧
      ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap))).1 =
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap))))
          (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (((D.fm u).fv i v c).comp e.toLinearMap)
              ((Tf.lv i hi).prk v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ⟨_, hx⟩)) →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ.1 * γ'.1).1 (clsCrd D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap)))) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (mulLat (γ.1 * γ'.1).1 (clsCrd D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap)))) = Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (clsCrd D u i hi c) ∧
      bc (prV (E := D.host.E) (Tf.atT.eV v).1) (((Tf.cls i hi).y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ.1 * γ'.1) *
        ((Tf.cls i hi).y ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap))).1) ∈ stabFun _ ((Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def RDnLocV (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ((D.fm u).te i v c) = 1 →
    ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    ∃ e : (D.fm u).lv i v ((D.fm u).dn i v c g) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk i v c,
      (D.fm u).fv i v ((D.fm u).dn i v c g) = g.comp e.toLinearMap ∧
      ∀ (z : ↥(Ld D u i hi ((D.fm u).dn i v c g))),
        (Tf.lv i hi).pr v ((D.fm u).dn i v c g) z = e.symm ((D.fm u).te i v c) →
      ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))).1 =
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g)) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g) ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi ((D.fm u).dn i v c g)),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (D.fm u).fv i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v ((D.fm u).dn i v c g) ⟨_, hx⟩)) →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ'.1 * γ.1).1 (clsCrd D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (mulLat (γ'.1 * γ.1).1 (clsCrd D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) = Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (clsCrd D u i hi c) ∧
      bc (prV (E := D.host.E) (Tf.atT.eV v).1) (((Tf.cls i hi).y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ'.1 * γ.1) *
        ((Tf.cls i hi).y ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))).1) ∈ stabFun _ ((Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem rupLocM_of_V (Tf : FormsTied D u) (h : RUpLocV Tf) : RUpLocM Tf := by
  intro i hi v c z hz γ η κ hsup hrel hl1 hl2 hfun
  obtain ⟨e, he1, he2⟩ := h i hi v c z hz γ η κ hsup hrel hl1 hl2 hfun
  refine ⟨e, he1, fun γ' η' κ' hsup' hrel' hl1' hfun' => ?_⟩
  obtain ⟨hP, hQ, hF⟩ := he2 γ' η' κ' hsup' hrel' hl1' hfun'
  exact rlv_comp_mem Tf i hi v _ _ _ γ γ' η η' κ κ' hsup hsup' hrel hrel' hP hQ hF

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem rdnLocM_of_V (Tf : FormsTied D u) (h : RDnLocV Tf) : RDnLocM Tf := by
  intro i hi v c g hg γ' η' κ' hsup' hrel' hl1' hfun'
  obtain ⟨e, he1, he2⟩ := h i hi v c g hg γ' η' κ' hsup' hrel' hl1' hfun'
  refine ⟨e, he1, fun z hz γ η κ hsup hrel hl1 hl2 hfun => ?_⟩
  obtain ⟨hP, hQ, hF⟩ := he2 z hz γ η κ hsup hrel hl1 hl2 hfun
  exact rlv_comp_mem Tf i hi v _ _ _ γ' γ η' η κ' κ hsup' hsup hrel' hrel hP hQ hF

set_option maxHeartbeats 2000000 in

theorem rlv_upDn_dualP (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c1 c2 : (D.mem u).C.cls i)
    (γ γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hl1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi c1)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c))
    (hl1' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c1)) :
    Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ.1 * γ'.1).1 (Ld D u i hi c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c) :=
  rlv_chainP _ γ.1.1 γ'.1.1 hl1 hl1'

set_option maxHeartbeats 2000000 in

theorem rlv_dnUp_latP (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c2 c3 : (D.mem u).C.cls i)
    (γ' γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hl1' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hl1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi c3)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c2)) :
    Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ'.1 * γ.1).1 (clsCrd D u i hi c3)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) :=
  rlv_chainP _ γ'.1.1 γ.1.1 hl1' hl1

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
