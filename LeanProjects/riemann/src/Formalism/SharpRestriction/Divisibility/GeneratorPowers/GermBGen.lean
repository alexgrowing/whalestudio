import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Jet

variable {S ι : Type} [CommRing S]

theorem jet_exists_nil (m : ℕ) (a : Jet S ι m) : ∃ c : S, IsNilpotent (a - algebraMap S (Jet S ι m) c) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨MvPolynomial.constantCoeff p, m + 1, ?_⟩
  have h : Ideal.Quotient.mk (orig S ι ^ (m + 1)) p - algebraMap S (Jet S ι m) (MvPolynomial.constantCoeff p) =
      Ideal.Quotient.mk _ (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) := by
    rw [map_sub]
    rfl
  rw [h, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (sub_const_mem_orig p) _

instance jet_isLocalRing [IsLocalRing S] (m : ℕ) : IsLocalRing (Jet S ι m) := by
  have : Nontrivial (Jet S ι m) := (jetAug : Jet S ι m →ₐ[S] S).toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨c, hc⟩ := jet_exists_nil (ι := ι) m a
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h | h
  · left
    have := hc.isUnit_add_left_of_commute (h.map (algebraMap S (Jet S ι m))) (Commute.all _ _)
    simpa using this
  · right
    have := hc.neg.isUnit_add_left_of_commute (h.map (algebraMap S (Jet S ι m))) (Commute.all _ _)
    convert this using 1
    rw [map_sub, map_one]
    ring

end Jet

section Gen

variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

def cgen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j0 : K → L.ι) (h0 : LB.wchart L φ j0 = ⊤) : LB.Gen (LB.LinComb L φ ε) :=
  ⟨fun j => res (le_inf le_rfl (by rw [h0]; exact le_top) : LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j0)
    ((LB.LinComb L φ ε).g j j0)⟩

theorem cgen_isGen (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j0 : K → L.ι) (h0 : LB.wchart L φ j0 = ⊤) :
    (cgen L φ ε j0 h0).IsGen := fun i j => unit_ext fun y hy => by
  have h0y : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j0 := by rw [h0]; trivial
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans ((gm_linComb L φ ε (𝟙 _) y i j0 hy.1 h0y).trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 _) y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans ((gm_res _ y _ hy.2 _).trans (gm_linComb L φ ε (𝟙 _) y j j0 hy.2 h0y))))).symm
  exact (trF_trans hL φ ε (𝟙 _) y hy.1 hy.2 h0y).symm

def cv {Z : Scheme.{0}} (i0 : L.ι) (z : Z) (J : (Z ⟶ X) → L.ι) (ψ : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z (L.U (J ψ) ⊓ L.U i0) (L.g (J ψ) i0)

theorem val_cgen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i0 : L.ι) (h0 : LB.wchart L φ (fun _ => i0) = ⊤) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    val (cgen L φ ε (fun _ => i0) h0) r z J = ∏ k, cv L i0 z J (r ≫ φ k) ^ ε k :=
  (gm_res r z _ (hJ.mem φ r) _).trans (gm_linComb L φ ε r z _ _ (hJ.mem φ r) (by rw [h0]; trivial))

theorem exists_ratio (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ u : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      val t r z J = gm r z ⊤ u * val t' r z J := by
  obtain ⟨s, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ hU => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [h U hU]
      simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ t')) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ ht
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ ht'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (s.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e1 := hv Z r z J hJ
  rw [val_mul hJ, val_inv, val_of s r z J PEmpty.elim (fun k => k.elim)] at e1
  have e2 := (gm_res r z le trivial (s.s PEmpty.elim)).trans e1
  exact mul_inv_eq_iff_eq_mul.1 e2.symm

def divLin (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε'))) :
    LB.Gen (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε fun k => -ε' k)) :=
  ⟨fun j => res (fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩ :
    LB.wchart L (Sum.elim φ φ') j ≤ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr))
    (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩

theorem gm_divLC (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (p q : (K → L.ι) × (K' → L.ι)) (y : Y) (hp : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U p)
    (hq : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U q) :
    gm (𝟙 Y) y _ ((LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).g p q) =
      trF φ ε (𝟙 Y) y p.1 q.1 * (trF φ' ε' (𝟙 Y) y p.2 q.2)⁻¹ := by
  have hpq : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U p ⊓
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U q := ⟨hp, hq⟩
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ y _ hpq _).trans
    (gm_linComb L φ ε (𝟙 _) y p.1 q.1 hp.1 hq.1)) ((map_inv _ _).trans (congrArg _ ((gm_res _ y _ hpq _).trans
      (gm_linComb L φ' ε' (𝟙 _) y p.2 q.2 hp.2 hq.2)))))

theorem divLin_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε'))) (hw : w.IsGen) :
    (divLin L φ ε φ' ε' w).IsGen := fun i j => unit_ext fun y hy => by
  have le : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr) := fun _ _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩
  have hi := le i hy.1
  have hj := le j hy.2
  have hij : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (i ∘ Sum.inl, i ∘ Sum.inr) ⊓
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr) := ⟨hi, hj⟩
  have hw' := (gm_res (𝟙 Y) y _ hij _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hw (i ∘ Sum.inl, i ∘ Sum.inr)
    (j ∘ Sum.inl, j ∘ Sum.inr))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hij _))))
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (hw'.trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm
  refine congrArg₂ (· * ·) ((gm_divLC L φ ε φ' ε' _ _ y hi hj).trans ?_) rfl
  refine Eq.trans ?_ (gm_linComb L _ _ (𝟙 _) y i j hy.1 hy.2).symm
  rw [Fintype.prod_sum_type]
  simp only [trF, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

end Gen

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
