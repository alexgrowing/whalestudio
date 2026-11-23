import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

theorem hecke_induction {p : (G → ℂ) → Prop} (h0 : p 0)
    (hadd : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, p f → p f' → p (f + f'))
    (hind : ∀ (r : ℂ) (g : G), p (r • dosetInd ℂ K g)) {f : G → ℂ} (hf : f ∈ Hecke ℂ K) : p f := by
  classical
  obtain ⟨e, he⟩ := Final.HeckeBasis G K ℂ
  suffices ∀ a, p (e.symm a) by simpa using this (e ⟨f, hf⟩)
  intro a
  induction a using Finsupp.induction_linear with
  | zero => simpa using h0
  | add a b ha hb => rw [map_add]; exact hadd _ (e.symm a).2 _ (e.symm b).2 ha hb
  | single c r =>
    obtain ⟨g, rfl⟩ : ∃ g, DoubleCoset.mk K K g = c := Quotient.exists_rep c
    convert hind r g
    funext x
    rw [← he, e.apply_symm_apply, Finsupp.single_apply, Pi.smul_apply, dosetInd, Set.indicator_apply]
    have : DoubleCoset.mk K K g = DoubleCoset.mk K K x ↔ x ∈ DoubleCoset.doubleCoset g (K : Set G) K := by
      rw [DoubleCoset.eq, DoubleCoset.mem_doubleCoset]; rfl
    by_cases hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) K
    · simp [hx, this.2 hx]
    · simp [hx, mt this.1 hx]

theorem heckeVec_add (hK : IsCommensurated K) (ρ : Representation ℂ G V) {f f' : G → ℂ} (hf : f ∈ Hecke ℂ K)
    (hf' : f' ∈ Hecke ℂ K) (x : V) : heckeVec ρ K (f + f') x = heckeVec ρ K f x + heckeVec ρ K f' x := by
  simp only [heckeVec, Pi.add_apply, add_smul]
  exact finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf' ρ x)

theorem heckeVec_smul (hK : IsCommensurated K) (ρ : Representation ℂ G V) (r : ℂ) {f : G → ℂ} (hf : f ∈ Hecke ℂ K)
    (x : V) : heckeVec ρ K (r • f) x = r • heckeVec ρ K f x := by
  simp only [heckeVec, Pi.smul_apply, smul_eq_mul, mul_smul]
  exact (smul_finsum' r (finite_heckeVec hK hf ρ x)).symm

theorem dosetInd_comp (e : G ≃* H) {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K') (t : H) :
    dosetInd ℂ K' t ∘ e = dosetInd ℂ K (e.symm t) := by
  funext g
  have : e g ∈ DoubleCoset.doubleCoset t (K' : Set H) K' ↔ g ∈ DoubleCoset.doubleCoset (e.symm t) (K : Set G) K := by
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨e.symm a, (hK _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), e.injective (by simpa using h)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨e a, (hK _).1 ha, e b, (hK _).1 hb, by simp⟩
  by_cases hg : g ∈ DoubleCoset.doubleCoset (e.symm t) (K : Set G) K
  · simp [dosetInd, hg, this.2 hg]
  · simp [dosetInd, hg, mt this.1 hg]

theorem dosetInd_mul {a b : G} (ha : a ∈ K) (hb : b ∈ K) (t : G) : dosetInd ℂ K (a * t * b) = dosetInd ℂ K t := by
  rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b, hb, rfl⟩)]

end Generic

section Unitary

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
  {σ : w.adicCompletion E →+* w.adicCompletion E} {n q : ℕ} {ϖ : w.adicCompletion E}
  {V : Type} [AddCommGroup V] [Module ℂ V]

open GlobalTheory.InertThetaCompare in

theorem cartanU (hU : IsUnramInv ϖ σ q) (g : GU σ n) : ∃ (d : Fin n → ℤ) (t : GU σ n), Antitone d ∧
    t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) ∧ ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g = k₁ * t * k₂ := by
  have hϖ : IsUnifV E w ϖ := hU.2.2.2.1
  obtain ⟨d, hd, k₁, h₁, k₂, h₂, e⟩ := Final.CartanDecomp E w n ϖ (mem_Ov_of_isUnifV hϖ) hϖ g.1
  obtain ⟨h, hh, eh⟩ := exists_antiJ_frame hU n
  have hh' : h ∈ GLint (Fin n) (Ov E w) := hh
  have hd' : ∀ i : Fin n, (List.ofFn d).getD i.1 0 = d i := fun i => by simp [List.getD_eq_getElem?_getD]
  have hG : Good n (List.ofFn d) := good_of_unitary hU (π := ϖ) hϖ (by simp)
    (List.pairwise_ofFn.2 fun i j hij => hd hij.le)
    (GlobalTheory.InertDoubleCoset.conj_mem_UJ σ (GlobalTheory.InertDoubleCoset.inv_frame σ eh) g.2)
    ⟨h * k₁, mul_mem hh' h₁, k₂ * h⁻¹, mul_mem h₂ (inv_mem hh'), by
      simp only [Units.val_mul, e, hd', inv_inv, Matrix.mul_assoc]; rfl⟩
  obtain ⟨t, ht⟩ := exists_diag hU hG
  simp only [hd'] at ht
  exact ⟨d, t, hd, ht, dc_GU hU (a := k₁) (b := k₂) h₁ h₂ (Units.ext (by simp only [Units.val_mul, ht]; exact e))⟩

theorem isSatVecU_of_diag (hU : IsUnramInv ϖ σ q) {ρ : Representation ℂ (GU σ n) V} {x : V} {α : Fin (n / 2) → ℂˣ}
    (h0 : x ≠ 0) (hx : x ∈ fixed ρ (KU σ n))
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      heckeVec ρ (KU σ n) (dosetInd ℂ (KU σ n) t) x = SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) • x) :
    IsSatVecU ϖ q ρ x α := by
  obtain ⟨y, hy⟩ := (hasSatU_psFunU hU α).exists_vec
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hm := Final.DosetIndMem _ (KU σ n) ℂ
  refine ⟨h0, hx, fun f hf => ?_⟩
  refine hecke_induction (K := KU σ n)
    (p := fun f => heckeVec ρ (KU σ n) f x = SatU ϖ q f (fun i => (α i : ℂ)) • x) ?_ ?_ ?_ hf
  · simp [heckeVec, SatU]
  · intro f hf f' hf' h1 h2
    have := hy.2.2 _ (add_mem hf hf')
    rw [heckeVec_add hK _ hf hf', hy.2.2 _ hf, hy.2.2 _ hf', ← add_smul] at this
    rw [heckeVec_add hK _ hf hf', h1, h2, ← add_smul, smul_left_injective ℂ hy.1 this]
  · intro r g
    obtain ⟨d, t, hd, ht, k₁, h₁, k₂, h₂, rfl⟩ := cartanU hU g
    rw [dosetInd_mul h₁ h₂]
    have := hy.2.2 _ (Submodule.smul_mem _ r (hm t))
    rw [heckeVec_smul hK _ r (hm t), hy.2.2 _ (hm t), smul_smul] at this
    rw [heckeVec_smul hK _ r (hm t), h d t hd ht, smul_smul, smul_left_injective ℂ hy.1 this]

end Unitary

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]

def IsEigenSys (h : w.under (𝓞 F) = v) (ρ : Representation ℂ (GLoc σ J v) V) (x : V) (c : List ℤ → ℂ) : Prop :=
  ∀ (a : GL (Fin n) (w.adicCompletion E)) (g : GLoc σ J v) (d : Fin n → ℤ) (u : Fin n → w.adicCompletion E),
    IsFrameAt w L a → Antitone d → (∀ i, Valued.v (u i) = WithZero.exp (-d i)) →
    (a⁻¹ * locMat σ J h g * a).1 = Matrix.diagonal u →
    heckeVec ρ (stabLoc σ J L v) (dosetInd ℂ (stabLoc σ J L v) g) x = c (List.ofFn d) • x

variable {σ J L} {h : w.under (𝓞 F) = v} {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {c : List ℤ → ℂ}
  {B : Multiset ℂˣ}

theorem IsEigenSys.split (hc : IsEigenSys σ J L h ρ x c) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    {e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)} (he : IsSplitChart σ J L h e) {ϖ : w.adicCompletion E}
    (hϖ : IsUnifV E w ϖ) {j : ℕ} (hj : j ≤ n) :
    heckeVec (ρ.comp e.symm.toMonoidHom) (KGL w n) (Tj ℂ n (Ov E w) ϖ j) x =
      c (List.replicate j 1 ++ List.replicate (n - j) 0) • x := by
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  let t : GL (Fin n) (w.adicCompletion E) := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (by
    rw [diagJ, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs <;> simp [h0])
  have ht : Tj ℂ n (Ov E w) ϖ j = dosetInd ℂ (KGL w n) t := by
    rw [Tj, dosetInd]
    congr 1
    ext g
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, Units.ext e⟩,
      fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, congrArg Units.val e⟩⟩
  obtain ⟨⟨a, ha, e1⟩, e2⟩ := he
  rw [heckeVec_comp_symm e e2 (Tj_mem_hecke hϖ j).1 hx, ht, dosetInd_comp e e2,
    hc a (e.symm t) (fun i => if i.1 < j then 1 else 0) (fun i => if i.1 < j then ϖ else 1) ha
      (fun i k hik => ?_) (fun i => ?_) (by rw [← e1, e.apply_symm_apply]; rfl)]
  · congr 2
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    by_cases hi : i < j <;> simp [hi, List.getElem_append]
  · have : i.1 ≤ k.1 := hik
    dsimp only
    split_ifs <;> omega
  · split_ifs
    · exact hϖ
    · simp

theorem IsEigenSys.inert (hc : IsEigenSys σ J L h ρ x c) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    {τ : w.adicCompletion E →+* w.adicCompletion E} {e : GLoc σ J v ≃* GU τ n} (he : IsInertChart σ J L h τ e)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {d : Fin n → ℤ} {t : GU τ n} (hd : Antitone d)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    heckeVec (ρ.comp e.symm.toMonoidHom) (KU τ n) (dosetInd ℂ (KU τ n) t) x = c (List.ofFn d) • x := by
  obtain ⟨-, ⟨a, ha, -, e1⟩, e2⟩ := he
  rw [heckeVec_comp_symm e e2 (Final.DosetIndMem _ _ ℂ t).1 hx, dosetInd_comp e e2,
    hc a (e.symm t) d _ ha hd (fun i => ?_) (by rw [← e1, e.apply_symm_apply, ht])]
  rw [map_zpow₀, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hϖ, ← WithZero.exp_zsmul]
  simp

theorem IsEigenSys.isSysParam (hc : IsEigenSys σ J L h ρ x c) (hB : IsParamVec σ J L h ρ x B) :
    IsSysParam σ n h c B := by
  have hx := hB.mem_fixed
  rcases hB with ⟨hv, e, he, hB⟩ | ⟨hw, τ, ϖ, e, α, hU, he, hB, rfl⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
    exact Or.inl ⟨hv, hB.2.2.1, fun j hj =>
      smul_left_injective ℂ hB.1 ((hc.split hx he hϖ hj).symm.trans (hB.2.2.2 ϖ hϖ j hj))⟩
  · exact Or.inr ⟨hw, τ, ϖ, α, hU, he.1, rfl, fun d t hd ht => smul_left_injective ℂ hB.1
      ((hc.inert hx he hU.2.2.2.1 hd ht).symm.trans (hB.2.2 _ (Final.DosetIndMem _ _ ℂ t)))⟩

theorem IsEigenSys.isParamVec (hc : IsEigenSys σ J L h ρ x c) (h0 : x ≠ 0) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    (hs : IsSplit (E := E) v → ∃ e, IsSplitChart σ J L h e)
    (hi : IsInertAt F E v w → ∀ τ, IsConjAt σ h τ → ∃ e, IsInertChart σ J L h τ e)
    (hB : IsSysParam σ n h c B) : IsParamVec σ J L h ρ x B := by
  rcases hB with ⟨hv, h1, h2⟩ | ⟨hw, τ, ϖ, α, hU, hτ, rfl, h2⟩
  · obtain ⟨e, he⟩ := hs hv
    exact Or.inl ⟨hv, e, he, h0, (mem_fixed_comp_symm e he.2).2 hx, h1, fun ϖ hϖ j hj => by
      rw [hc.split hx he hϖ hj, h2 j hj]⟩
  · obtain ⟨e, he⟩ := hi hw τ hτ
    exact Or.inr ⟨hw, τ, ϖ, e, α, hU, he, isSatVecU_of_diag hU h0 ((mem_fixed_comp_symm e he.2.2).2 hx)
      fun d t hd ht => by rw [hc.inert hx he hU.2.2.2.1 hd ht, h2 d t hd ht], rfl⟩

end Place

end GlobalTheory.LFun

end
