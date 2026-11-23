import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxProduct

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.Supp

open GlobalTheory.CompanionTheory.Sa2Prod

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem trunc_mul_trunc {c d : R} (h : c * d = 0) {A : Matrix n n R} (hA : (c + d) • (A - 1) = A - 1) :
    trunc c A * trunc d A = A := by
  have e : trunc c A * trunc d A = 1 + (c + d) • (A - 1) + (c * d) • ((A - 1) * (A - 1)) := by
    unfold trunc
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, add_smul, smul_add]
    rw [mul_comm d c]
    abel
  rw [e, h, zero_smul, add_zero, hA]
  abel

end Ring

section Idem

variable {F : Type} [Field F] [NumberField F]

theorem idem_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {a : AF F}
    (ha : IsPlacesIdem S₁ S₂ a) : a * a = a := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_mul]
    change fstA F a w * fstA F a w = fstA F a w
    by_cases h : w ∈ S₁
    · rw [ha.1 w h, one_mul]
    · rw [ha.2.1 w h, zero_mul]
  · rw [map_mul, map_mul]
    by_cases h : v ∈ S₂
    · rw [ha.2.2.1 v h, one_mul]
    · rw [ha.2.2.2 v h, zero_mul]

theorem idem_orth {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂) :
    a * b = 0 := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_mul, map_zero]
    change fstA F a w * fstA F b w = 0
    by_cases h : w ∈ A₁
    · rw [hb.2.1 w (Finset.disjoint_left.1 h₁ h), mul_zero]
    · rw [ha.2.1 w h, zero_mul]
  · rw [map_mul, map_mul, map_zero, map_zero]
    by_cases h : v ∈ A₂
    · rw [hb.2.2.2 v (Finset.disjoint_left.1 h₂ h), mul_zero]
    · rw [ha.2.2.2 v h, zero_mul]

theorem idem_eq_add [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b δ : AF F}
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂)
    (hδ : IsPlacesIdem (A₁ ∪ B₁) (A₂ ∪ B₂) δ) : δ = a + b := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_add]
    change fstA F δ w = fstA F a w + fstA F b w
    by_cases h : w ∈ A₁
    · rw [hδ.1 w (Finset.mem_union_left _ h), ha.1 w h, hb.2.1 w (Finset.disjoint_left.1 h₁ h), add_zero]
    · by_cases h' : w ∈ B₁
      · rw [hδ.1 w (Finset.mem_union_right _ h'), ha.2.1 w h, hb.1 w h', zero_add]
      · rw [hδ.2.1 w (by simp [h, h']), ha.2.1 w h, hb.2.1 w h', add_zero]
  · rw [map_add, map_add]
    by_cases h : v ∈ A₂
    · rw [hδ.2.2.1 v (Finset.mem_union_left _ h), ha.2.2.1 v h, hb.2.2.2 v (Finset.disjoint_left.1 h₂ h), add_zero]
    · by_cases h' : v ∈ B₂
      · rw [hδ.2.2.1 v (Finset.mem_union_right _ h'), ha.2.2.2 v h, hb.2.2.1 v h', zero_add]
      · rw [hδ.2.2.2 v (by simp [h, h']), ha.2.2.2 v h, hb.2.2.2 v h', add_zero]

theorem idem_empty {a : AF F} (ha : IsPlacesIdem (∅ : Finset (InfinitePlace F))
    (∅ : Finset (HeightOneSpectrum (𝓞 F))) a) : a = 0 := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_zero]
    exact ha.2.1 w (Finset.notMem_empty w)
  · rw [map_zero, map_zero]
    exact ha.2.2.2 v (Finset.notMem_empty v)

end Idem

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem supp_split (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {a b : AF F}
    (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) {g : HA (AF F) σ J} (hg : g ∈ SUSupp σ J (a + b)) :
    ∃ x ∈ SUSupp σ J a, ∃ y ∈ SUSupp σ J b, g = x * y := by
  have ha' : algebraMap (AF F) (AF F ⊗[F] E) a * algebraMap (AF F) (AF F ⊗[F] E) a =
      algebraMap (AF F) (AF F ⊗[F] E) a := by rw [← map_mul, ha]
  have hb' : algebraMap (AF F) (AF F ⊗[F] E) b * algebraMap (AF F) (AF F ⊗[F] E) b =
      algebraMap (AF F) (AF F ⊗[F] E) b := by rw [← map_mul, hb]
  refine ⟨truncHA σ J ha' g, truncHA_mem σ J ha' hg.1, truncHA σ J hb' g, truncHA_mem σ J hb' hg.1, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  refine (trunc_mul_trunc (c := algebraMap (AF F) (AF F ⊗[F] E) a) (d := algebraMap (AF F) (AF F ⊗[F] E) b)
    (by rw [← map_mul, hab, map_zero]) ?_).symm
  ext i j
  have := hg.2 i j
  rw [map_add] at this
  rw [Matrix.smul_apply, smul_eq_mul]
  exact this

theorem supp_le_of_disjoint [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J))
    {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b δ : AF F}
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂)
    (hδ : IsPlacesIdem (A₁ ∪ B₁) (A₂ ∪ B₂) δ) (hNa : SUSupp σ J a ⊆ N) (hNb : SUSupp σ J b ⊆ N) :
    SUSupp σ J δ ⊆ N := by
  intro g hg
  rw [idem_eq_add ha hb h₁ h₂ hδ] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := supp_split σ J (idem_self ha) (idem_self hb) (idem_orth ha hb h₁ h₂) hg
  exact N.mul_mem (hNa hx) (hNb hy)

theorem supp_zero_le (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J)) :
    SUSupp σ J (0 : AF F) ⊆ N := by
  intro g hg
  have h : g = 1 := by
    refine Subtype.ext (Units.ext ?_)
    ext i j
    have := hg.2 i j
    rw [map_zero, zero_mul] at this
    exact (sub_eq_zero.1 this.symm)
  rw [h]
  exact N.one_mem

theorem supp_le_of_single : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J))
    {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} {δ : AF F},
    IsPlacesIdem T₁ T₂ δ → (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → SUSupp σ J e ⊆ N) →
    (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → SUSupp σ J e ⊆ N) → SUSupp σ J δ ⊆ N := by
  intro F E _ _ _ _ _ σ M J N T₁ T₂ δ hδ h₁ h₂
  classical
  have base : ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∈ S, ∀ e : AF F, IsPlacesIdem ∅ {v} e → SUSupp σ J e ⊆ N) →
      ∀ d : AF F, IsPlacesIdem ∅ S d → SUSupp σ J d ⊆ N := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ d hd
      rw [idem_empty hd]
      exact supp_zero_le σ J N
    | insert v s hv ih =>
      intro hS d hd
      obtain ⟨e, he⟩ := StrongApprox.exists_isPlacesIdem (F := F) ∅ {v}
      obtain ⟨d', hd'⟩ := StrongApprox.exists_isPlacesIdem (F := F) ∅ s
      refine supp_le_of_disjoint σ J N he hd' (Finset.disjoint_empty_left _)
        (Finset.disjoint_singleton_left.2 hv) ?_ (hS v (Finset.mem_insert_self v s) e he)
        (ih (fun u hu => hS u (Finset.mem_insert_of_mem hu)) d' hd')
      rwa [Finset.empty_union, ← Finset.insert_eq]
  have main : ∀ (S : Finset (InfinitePlace F)), (∀ w ∈ S, ∀ e : AF F, IsPlacesIdem {w} ∅ e → SUSupp σ J e ⊆ N) →
      ∀ d : AF F, IsPlacesIdem S T₂ d → SUSupp σ J d ⊆ N := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ d hd
      exact base T₂ h₂ d hd
    | insert w s hw ih =>
      intro hS d hd
      obtain ⟨e, he⟩ := StrongApprox.exists_isPlacesIdem (F := F) {w} ∅
      obtain ⟨d', hd'⟩ := StrongApprox.exists_isPlacesIdem (F := F) s T₂
      refine supp_le_of_disjoint σ J N he hd' (Finset.disjoint_singleton_left.2 hw)
        (Finset.disjoint_empty_left _) ?_ (hS w (Finset.mem_insert_self w s) e he)
        (ih (fun u hu => hS u (Finset.mem_insert_of_mem hu)) d' hd')
      rwa [Finset.empty_union, ← Finset.insert_eq]
  exact main T₁ h₁ δ hδ

end Main

end GlobalTheory.CompanionTheory.SaGen.Supp
