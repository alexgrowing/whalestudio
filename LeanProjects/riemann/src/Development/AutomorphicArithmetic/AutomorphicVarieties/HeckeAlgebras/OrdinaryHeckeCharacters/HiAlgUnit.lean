import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.HeckeLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.InvMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem hiAlg_unit {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] (Y L : Submodule A M)
    [Module.Finite A Y] [Module.Finite A L] (hLY : L ≤ Y) (op : ι → Module.End A M) [h : Fact (CommOn L op)] (i : ι)
    (hb : Set.BijOn (op i) Y Y) : IsUnit (heckeGen L op i) := by
  have hYs : ∀ y ∈ Y, op i y ∈ Y := fun y hy => hb.mapsTo hy
  let fY : Module.End A Y := (op i).restrict hYs
  have hfYb : Function.Bijective fY := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hb.injOn x.2 y.2 (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx, hxy⟩ := hb.surjOn y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨u, hu⟩ := (Module.End.isUnit_iff fY).2 hfYb
  have hinv : ((u⁻¹ : (Module.End A Y)ˣ) : Module.End A Y) ∈ Algebra.adjoin A ({fY} : Set (Module.End A Y)) :=
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.invMem A Y _ u (by rw [hu]; exact Algebra.subset_adjoin rfl)
  have hpres : ∀ g ∈ Algebra.adjoin A ({fY} : Set (Module.End A Y)), ∀ y : Y, (y : M) ∈ L → ((g y : Y) : M) ∈ L := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      intro y hy
      exact h.out.1 i y hy
    | algebraMap r =>
      intro y hy
      simpa using L.smul_mem r hy
    | add x z _ _ hx hz =>
      intro y hy
      simpa using L.add_mem (hx y hy) (hz y hy)
    | mul x z _ _ hx hz =>
      intro y hy
      exact hx _ (hz y hy)
  have hgL : Function.Bijective (heckeGen L op i : Module.End A L) := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hb.injOn (hLY x.2) (hLY y.2) (congrArg Subtype.val hxy)
    · intro y
      refine ⟨⟨(((u⁻¹ : (Module.End A Y)ˣ) : Module.End A Y) ⟨y, hLY y.2⟩ : M), hpres _ hinv _ y.2⟩, ?_⟩
      apply Subtype.ext
      have h1 := LinearMap.congr_fun u.mul_inv ⟨y, hLY y.2⟩
      rw [hu] at h1
      have h2 := congrArg Subtype.val h1
      exact h2
  obtain ⟨v, hv⟩ := (Module.End.isUnit_iff _).2 hgL
  have hmem : ((v⁻¹ : (Module.End A L)ˣ) : Module.End A L) ∈ heckeAlg L op :=
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.invMem A L (heckeAlg L op) v (by rw [hv]; exact (heckeGen L op i).2)
  refine ⟨⟨heckeGen L op i, ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    show (heckeGen L op i : Module.End A L) * _ = 1
    rw [← hv]
    exact v.mul_inv
  · apply Subtype.ext
    show _ * (heckeGen L op i : Module.End A L) = 1
    rw [← hv]
    exact v.inv_mul

private theorem hiAlg_top {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] (L : Submodule A M)
    (op : ι → Module.End A M) [h : Fact (CommOn L op)] : Algebra.adjoin A (Set.range (heckeGen L op)) = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro ⟨x, hx⟩ -
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj⟩ := hx
    have he : (⟨x, Algebra.subset_adjoin ⟨j, hj⟩⟩ : heckeAlg L op) = heckeGen L op j := by
      apply Subtype.ext
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      exact hj y
    rw [he]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    exact Subalgebra.algebraMap_mem _ r
  | add x z hx' hz' hx hz =>
    exact Subalgebra.add_mem _ hx hz
  | mul x z hx' hz' hx hz =>
    exact Subalgebra.mul_mem _ hx hz

private theorem hiAlg_abs {O A M ι : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing A] [Algebra O A]
    [Alg.IsCO O A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → O)
    (hc : CommOn Y op) (L : Submodule A M) (hL : L = locPart Y op fun i => algebraMap O A (a i)) [Fact (CommOn L op)] (hne : L ≠ ⊥)
    [Algebra O (heckeAlg L op)] [IsScalarTower O A (heckeAlg L op)] :
    ∃ _ : Alg.IsCO O (heckeAlg L op), (algebraMap A (heckeAlg L op)).Finite ∧
      (∀ b : A, (∀ y ∈ Y, b • y = 0 → y = 0) → ∀ t, algebraMap A (heckeAlg L op) b * t = 0 → t = 0) ∧
      (∀ i, heckeGen _ op i - algebraMap O (heckeAlg L op) (a i) ∈ maximalIdeal _) := by
  haveI : IsCNL A := IsCNL.ofCO O A
  subst hL
  obtain ⟨hT, hfin, hloc, hres, hgen, hnzd⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeLocal A M ι Y op
    (fun i => algebraMap O A (a i)) hc hne (heckeAlg (locPart Y op fun i => algebraMap O A (a i)) op)
    (Subalgebra.val _) Subtype.val_injective (Subalgebra.range_val _)
  have hCO : Alg.IsCO O (heckeAlg (locPart Y op fun i => algebraMap O A (a i)) op) := by
    refine UpperTheory.V.Alg.co_finite O A _ ?_
    intro x
    obtain ⟨c, hc'⟩ := hres x
    obtain ⟨d, hd⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := O) c
    refine ⟨d, ?_⟩
    have h2 := map_nonunit (algebraMap A (heckeAlg (locPart Y op fun i => algebraMap O A (a i)) op)) _ hd
    rw [IsScalarTower.algebraMap_apply O A _ d]
    have h3 := Ideal.add_mem _ hc' h2
    rw [map_sub, sub_add_sub_cancel] at h3
    exact h3
  refine ⟨hCO, RingHom.finite_algebraMap.2 hfin, ?_, ?_⟩
  · intro b hb t ht
    exact (mem_nonZeroDivisors_iff.1 (hnzd b hb)).1 t ht
  · intro i
    have h5 := hgen i (heckeGen _ op i) (fun y => rfl)
    rw [IsScalarTower.algebraMap_apply O A _ (a i)]
    exact h5

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Hi.hiAlg :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))], H.MK θ a K ≠ ⊥ → ∃ _ : Alg.IsCO c.O (H.TK θ a K), (algebraMap A (H.TK θ a K)).Finite ∧ (IsDomain A → ∀ b : A, b ≠ 0 → ∀ t : H.TK θ a K, algebraMap A (H.TK θ a K) b * t = 0 → t = 0) ∧ (∀ i, H.gen θ a K i - algebraMap c.O (H.TK θ a K) (a i) ∈ maximalIdeal (H.TK θ a K)) ∧ (∀ v j, IsUnit (H.gen θ a K (.inr (v, j)))) ∧ Algebra.adjoin A (Set.range (H.gen θ a K)) = ⊤ := by
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ a K _ hne
  haveI : Finite (IsLocalRing.ResidueField c.O) := by
    haveI := c.fin
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    exact IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hcY, hfY, hfrY, hMK⟩ := hiComm L Ω l n c H hAx A θ hθ K
  obtain ⟨-, hfM, -⟩ := hMK a
  haveI := hfY
  haveI := hfM
  haveI := hfrY
  have hP : ∀ (v : H.V) (k : ℕ), alV n H.Sl v k ∈ H.X.I.P := by
    intro v k
    unfold UpperTheory.V.Hi.alV UpperTheory.V.Hi.HSet.X
    dsimp only
    unfold UpperTheory.V.Hi.iwS UpperTheory.V.Hi.piIwa
    dsimp only
    unfold UpperTheory.V.Hi.piData
    dsimp only
    intro w _
    by_cases hw : w = v
    · subst hw
      simp only [Pi.mulSingle_eq_same]
      exact al_mem _ n k
    · simp only [Pi.mulSingle, Function.update, hw, dif_neg, not_false_eq_true, Pi.one_apply]
      exact (glIwa _ n).P.one_mem
  obtain ⟨-, -, hbij⟩ := ordFree _ _ _ H.X A H.m (H.τA A) θ hθ.cont (H.lev K) (hAx.fin K) (hθ.free K)
  obtain ⟨hCO, hfin, hnz, hres⟩ := hiAlg_abs (O := c.O) (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) a hcY
    (H.MK θ a K) rfl hne
  refine ⟨hCO, hfin, ?_, hres, ?_, hiAlg_top _ _⟩
  · intro hdom b hb t ht
    refine hnz b ?_ t ht
    intro y hy hby
    have h0 : b • (⟨y, hy⟩ : H.X.Ord (H.τA A) θ (H.lev K)) = 0 := Subtype.ext hby
    rcases smul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 hb
    · exact congrArg Subtype.val h1
  · intro v j
    exact hiAlg_unit (H.X.Ord (H.τA A) θ (H.lev K)) (H.MK θ a K) inf_le_left (H.op A) (.inr (v, j))
      (hbij _ (hP v (j + 1)))
