import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstFamComponentsBasisExpansion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SectionsEquivAnArcTheta

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ConstThetaSections

section Translate

open FrameValue TwistedTheta ConstFam SymmetricSemicharacter CubeValues ReciprocityTheory.ChartRestriction.G.DVR

def frU {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (hL : L.IsLB) (w : Fin g → ℂ) : ℂˣ :=
  Units.mk0 _ (u.fr_ne _ w (le_chartAt hL (u.ex w).left))

abbrev stU : ℂˣ →* ((Sp ℂ).presheaf.stalk pt)ˣ := Units.map toStalk.toMonoidHom

theorem val_eq_stU {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} (hL : L.IsLB)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} (hz : IsLift u φ y z) {c : ℂˣ} (hc : genVal u hL t y z = c) :
    val t y pt (chartAt hL) = stU (c * ∏ k, frU u hL (z k) ^ ε k) := by
  have h := le_wchart_chartAt hL φ y
  refine Units.ext (((gs_unit y pt _ (h trivial) _).symm.trans (gs_eq_toStalk _ _ h _)).trans
    (congrArg toStalk ?_))
  refine ((div_eq_iff (frameProd_ne_zero hz ε h)).1 hc).trans ?_
  have := map_prod (Units.coeHom ℂ) (fun k => frU u hL (z k) ^ ε k) Finset.univ
  simp only [map_zpow, Units.coeHom_apply] at this
  rw [Units.val_mul, this]
  simp only [frameProd, hz _]
  rfl

variable {D : Out.DegPre ℂ} {g : ℕ} {u : HolUnif D.P.A D.P.L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem th_eq (h : u.IsAH Hm χ) (a b c : Fin g → ℂ) :
    th D (T := 𝟙_ (Over (Sp ℂ))) pt (chartAt D.P.isLB) (u.ex a) (u.ex b) (u.ex c) =
      stU (frU u D.P.isLB (a + b + c) * (frU u D.P.isLB (a + b))⁻¹ * (frU u D.P.isLB (a + c))⁻¹ *
        (frU u D.P.isLB (b + c))⁻¹ * frU u D.P.isLB a * frU u D.P.isLB b * frU u D.P.isLB c * (frU u D.P.isLB 0)⁻¹) := by
  refine (val_eq_stU D.P.isLB D.cub.t (isLift_cube u ![a, b, c]) (c := 1)
    (genVal_cube_of_face D.P.isLB h D.cub.t D.cub.isGen (D.cub.face 0) ![a, b, c])).trans (congrArg stU ?_)
  refine (_root_.one_mul _).trans ((prod_thK fun I => frU u D.P.isLB (∑ k ∈ I, ![a, b, c] k)).trans ?_)
  simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val]

theorem cubN_eq (h : u.IsAH Hm χ) (j : ℕ) (a m x : Fin g → ℂ) :
    cubN (th D (T := 𝟙_ (Over (Sp ℂ))) pt (chartAt D.P.isLB)) j (u.ex a) (u.ex m) (u.ex x) =
      stU (frU u D.P.isLB (a + j • m + x) * (frU u D.P.isLB (a + j • m))⁻¹ * (frU u D.P.isLB (a + x))⁻¹ *
        frU u D.P.isLB a * ((frU u D.P.isLB (m + x))⁻¹ * frU u D.P.isLB m * frU u D.P.isLB x *
          (frU u D.P.isLB 0)⁻¹) ^ j) := by
  induction j with
  | zero => simp [cubN]
  | succ n ih =>
    rw [cubN, Finset.prod_range_succ, ← cubN, ih, ← ex_nsmul, ← u.ex_add, th_eq h, ← map_mul, succ_nsmul,
      ← add_assoc a]
    refine congrArg stU ?_
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem jFK_jK : Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ = 𝟙 _ := by
  refine (TF_hom (R := ℂ) ℂ).trans ?_
  rw [show toF (R := ℂ) ℂ = RingHom.id ℂ from (IsScalarTower.algebraMap_eq ℂ (FractionRing ℂ) ℂ).symm,
    CommRingCat.ofHom_id, Spec.map_id]

theorem secVal_feTranslate (h : u.IsAH Hm χ) (hr : u.IsRig D.rig) (j : ℕ) {α mu : D.X} {ca cm : Fin g → ℂ}
    (ha : u.ex ca = D.c α) (hm : u.ex cm = D.c mu) {pa pm ps : ℂˣ}
    (ea : genVal u D.P.isLB (D.psi α) (Out.jFK (R := ℂ) ℂ) (fun _ => ca) = pa)
    (em : genVal u D.P.isLB (D.psi mu) (Out.jFK (R := ℂ) ℂ) (fun _ => cm) = pm)
    (es : genVal u D.P.isLB (D.psi (mu + α)) (Out.jFK (R := ℂ) ℂ) (fun _ => cm + ca) = ps)
    (s : SecBMod D j α) (z : Fin g → ℂ) :
    secVal u D.P.isLB (feTranslate D j mu α s) (u.ex z).left ![z, z + (ca + j • cm), ca + j • cm, 0] =
      secVal u D.P.isLB s (u.ex (z + cm)).left ![z + cm, z + cm + ca, ca, 0] * (pm ^ j * (ps * pm⁻¹ * pa⁻¹) : ℂˣ) := by
  have hL := D.P.isLB
  have hJ := good_chartAt hL
  have cp : ∀ x, cP D (𝟙_ (Over (Sp ℂ))) x = D.c x := fun x => by
    rw [cP, Subsingleton.elim (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _), Category.id_comp]
  have hc : u.ex (ca + j • cm) = D.c (α + j • mu) := by
    rw [u.ex_add, ex_nsmul, ha, hm, ← cp, ← cp, ← cp, cPoint_add, cPoint_nsmul]
  have hs : u.ex (cm + ca) = D.c (mu + α) := by rw [u.ex_add, ha, hm, ← cp, ← cp, ← cp, cPoint_add]
  have tr : (u.ex z).left ≫ (trB D mu).left = (u.ex (z + cm)).left :=
    congrArg (fun m : 𝟙_ (Over (Sp ℂ)) ⟶ D.P.A => m.left) (show u.ex z ≫ trB D mu = u.ex (z + cm) by
      rw [MonObj.comp_mul, Category.comp_id, comp_cP, cp, u.ex_add, hm])
  have hz : IsLift u (Sum.elim (D.famφB (α + j • mu)) (fun i => (trB D mu).left ≫ D.famφB α i)) (u.ex z).left
      (Sum.elim ![z, z + (ca + j • cm), ca + j • cm, 0] ![z + cm, z + cm + ca, ca, 0]) := by
    rintro (k | k)
    · exact isLift_fam hc z k
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) tr).trans (isLift_fam ha (z + cm) k))
  have e := sval_feTranslate D j mu α s (u.ex z).left hJ
  rw [tr] at e
  refine (secVal_eq_mul hL e (isLift_fam hc z) (isLift_fam ha (z + cm)) hz fun f => ?_).trans (congrArg _ ?_)
  · simp only [Out.DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
      Finset.prod_inv_distrib]
    rw [_root_.mul_left_comm, mul_inv_cancel, _root_.mul_one]
  have lp : ∀ x c, u.ex c = D.c x → IsLift u (fun _ : PUnit => Out.ptK (D.c x)) (Out.jFK (R := ℂ) ℂ) (fun _ => c) :=
    fun x c hx _ => by
      show Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ ≫ (D.c x).left = _
      rw [← Category.assoc, jFK_jK, hx]; exact Category.id_comp _
  have va := val_eq_stU hL _ (lp _ _ ha) ea
  have vm := val_eq_stU hL _ (lp _ _ hm) em
  have vs := val_eq_stU hL _ (lp _ _ hs) es
  have vr : val D.rigK (Out.jFK (R := ℂ) ℂ) pt (chartAt hL) = stU (frU u hL 0) := by
    refine (val_pull hJ _ _ _).trans ((congrArg (fun q => val (L := D.P.L) D.rig q pt (chartAt hL)) jFK_jK).trans ?_)
    refine (val_eq_stU hL D.rig (z := fun _ => 0) (fun _ => ?_) (c := 1) (genVal_rig hL hr)).trans ?_
    · rw [ex_zero, Hom.one_def]; simp [eSec]
    · simp
  let κ : 𝟙_ (Over (Sp ℂ)) ⟶ Out.TK ℂ := Over.homMk (Out.jFK (R := ℂ) ℂ) jFK_jK
  have v := val_feGen D j mu α (u.ex z) κ hJ
  rw [(cp α).trans ha.symm, (cp mu).trans hm.symm, cubN_eq h, th_eq h, val_tau D _ hJ, show κ.left = Out.jFK (R := ℂ) ℂ from rfl] at v
  erw [va, vm, vs, vr] at v
  obtain ⟨G, hG⟩ : IsUnit (genVal u hL (feGen D j mu α) _ _) := (genVal_ne_zero hL _ hz).isUnit
  have v' := val_eq_stU hL (feGen D j mu α) hz hG.symm
  simp only [← map_inv, ← map_pow, ← map_mul] at v
  have w := Units.map_injective (f := toStalk.toMonoidHom) toStalk.injective (v'.symm.trans v)
  refine hG.symm.trans (congrArg Units.val ?_)
  simp only [Out.DegPre.deltaε, Out.DegPre.famε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four,
    Matrix.cons_val, Fintype.prod_unique] at w
  rw [add_comm (ca + j • cm) z, add_comm cm z, show ca + z + cm = z + cm + ca by abel, add_comm cm ca] at w
  apply Additive.ofMul.injective
  have w' := congrArg Additive.ofMul w
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow] at w' ⊢
  linear_combination (norm := module) w'

end Translate

section Pull

open ConstFam FieldBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)

theorem valR_smul_pullB (j : ℕ) (α : a.D₀.X) (s : SecBMod a.D₀ j α) (r : PowerSeries k) (Z : Type) [CommRing Z]
    [IsLocalRing Z] (p : Sp Z ⟶ P.toPre.P.A.left) (κ : PowerSeries k →+* Z) (jf : Fin 4 → P.toPre.P.L.ι)
    (j₀ : Fin 4 → a.D₀.P.L.ι) (hp : p ≫ P.toPre.P.A.hom = spMap κ)
    (hi : ∀ i, ⊤ ≤ (p ≫ P.toPre.famφB (e α) i) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull φ) P.toPre.P.L).U (fun _ => j₀ i, jf i)) :
    ∃ u : Fin 4 → Zˣ, (∀ i, (u i : Z) = valR (p ≫ P.toPre.famφB (e α) i) _ (w.s (fun _ => j₀ i, jf i)).val) ∧
      (∏ i, u i ^ Out.DegPre.famε j i : Zˣ) * valR p (LB.wchart P.toPre.P.L (P.toPre.famφB (e α)) jf)
        (LB.Sec.f (r • pullB hW j α s : SecBMod P.toPre j (e α)) jf) =
      κ r * valR (p ≫ φ) (LB.wchart a.D₀.P.L (a.D₀.famφB α) j₀) (LB.Sec.f s j₀) := by
  choose u hu using fun i => FormalValue.isUnit_valR _ _ (hi i) (w.s (fun _ => j₀ i, jf i))
  refine ⟨u, hu, toStkA_injective ?_⟩
  have m : ∀ i, (p ≫ P.toPre.famφB (e α) i) (cpt Z) ∈ (a.D₀.P.L.pull φ).U (fun _ => j₀ i) ⊓ P.toPre.P.L.U (jf i) :=
    fun i => hi i trivial
  have m₁ : p (cpt Z) ∈ LB.wchart P.toPre.P.L (P.toPre.famφB (e α)) jf := Set.mem_iInter.2 fun i => (m i).2
  have m₂ : (p ≫ φ) (cpt Z) ∈ LB.wchart a.D₀.P.L (a.D₀.famφB α) j₀ := Set.mem_iInter.2 fun i =>
    (congrArg (fun q => q (p (cpt Z)) ∈ a.D₀.P.L.U (j₀ i)) (famφB_comp hW α i)).mp (mem_pull.1 (m i).1)
  have H₁ := secThrough_pullB hW j α s _ p (cpt Z) j₀ jf (fun i => mem_pull.1 (m i).1) (fun i => (m i).2)
  have H₂ : toStkA (cpt Z) (∏ i, u i ^ Out.DegPre.famε j i : Zˣ) =
      (∏ i, gw w (p ≫ P.toPre.famφB (e α) i) (cpt Z) (j₀ i) (jf i) ^ Out.DegPre.famε j i).val := by
    refine congrArg Units.val ((map_prod (Units.map (toStkA (cpt Z)).toMonoidHom) _ _).trans
      (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans (congrArg (· ^ _) (Units.ext ?_))))
    exact (congrArg (toStkA (cpt Z)) (hu i)).trans (toStkA_valR _ _ _ (hi i) _)
  have H₃ : constVal (p ≫ P.toPre.P.A.hom) (cpt Z) r = toStkA (cpt Z) (κ r) := by
    rw [hp, ← Category.id_comp (spMap κ)]
    exact (constVal_specMap _ κ _ r).trans (gs_eq (𝟙 _) _ ⊤ trivial _)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) H₂ ((FormalValue.toStkA_valR_eq_gs _ _ _
    ((top_le_iff_cpt _ _).2 m₁) _).trans (gs_smul P.toPre.P.A.hom p (cpt Z) _ m₁ r _))).trans (Eq.trans ?_
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) H₃.symm ((FormalValue.toStkA_valR_eq_gs _ _ _
    ((top_le_iff_cpt _ _).2 m₂) _).trans H₁))).symm))
  exact _root_.mul_left_comm _ _ _

end Pull

theorem exists_sum_sub_mem {S T : Type} {i : S → T} (hi : Function.Injective i) {n : S → ℕ} {c : S → ℂ}
    {h : T → ℂ⟦X⟧} (h₁ : ∀ mu, h (i mu) = PowerSeries.X ^ n mu * PowerSeries.C (c mu)) (h₂ : ∀ x, (∀ mu, i mu ≠ x) → h x = 0)
    {L : ℕ → Finset S} (hL : ∀ k mu, mu ∈ L k ↔ n mu = k) (e : ℕ) (F : Finset T) :
    ∃ F', F ⊆ F' ∧ (PowerSeries.X : ℂ⟦X⟧) ^ e ∣ ∑ x ∈ F', h x - PowerSeries.mk fun k => ∑ mu ∈ L k, c mu := by
  classical
  refine ⟨F ∪ ((Finset.range e).biUnion L).image i, Finset.subset_union_left,
    PowerSeries.X_pow_dvd_iff.2 fun k hk => ?_⟩
  rw [map_sub, map_sum, PowerSeries.coeff_mk, sub_eq_zero, ← Finset.sum_subset (s₁ := (L k).image i),
    Finset.sum_image hi.injOn]
  · refine Finset.sum_congr rfl fun mu hmu => ?_
    rw [h₁, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow, if_pos ((hL _ _).1 hmu).symm, _root_.one_mul]
  · exact (Finset.image_subset_image (Finset.subset_biUnion_of_mem L (Finset.mem_range.2 hk))).trans
      Finset.subset_union_right
  · intro x _ hx
    by_cases hx' : ∃ mu, i mu = x
    · obtain ⟨mu, rfl⟩ := hx'
      rw [h₁, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow, if_neg, zero_mul]
      exact fun hk' => hx (Finset.mem_image_of_mem _ ((hL _ _).2 hk'.symm))
    · rw [h₂ x fun mu e => hx' ⟨mu, e⟩, map_zero]

theorem algebraMap_mk_eq {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (j : ℕ) [NeZero j] (α : A.X)
    (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) {m : ℕ} (hm : ∀ mu, 0 ≤ (m : ℤ) + A.exponent j α mu) :
    algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (PowerSeries.mk fun k => ∑ mu ∈ A.level j α ((k : ℤ) - m), A.term j α th mu v) =
      HahnSeries.single (m : ℤ) (1 : ℂ) * A.FSum j α th v := by
  ext n
  rw [HahnSeries.coeff_single_mul, _root_.one_mul, AnArc.coeff_FSum, LaurentSeries.coe_algebraMap,
    PowerSeries.coeff_coe]
  split_ifs with hn
  · refine (Finset.sum_eq_zero fun mu hmu => ?_).symm
    have := hm mu
    rw [A.mem_level.1 hmu] at this
    omega
  · rw [PowerSeries.coeff_mk, Int.natCast_natAbs, abs_of_nonneg (not_lt.1 hn)]

end GlobalTheory.ConstThetaSections
