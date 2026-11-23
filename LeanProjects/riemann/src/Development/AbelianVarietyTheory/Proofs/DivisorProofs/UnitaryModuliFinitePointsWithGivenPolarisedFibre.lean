import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegerRingActionsPrincipallyPolarisedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliGeometricPointEqOfSameFibreActionLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationPartBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMinQF
open ReciprocityTheory.ChartRestriction.G.DVR

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

theorem sab_gen (t : SAB H S) (a : 𝓞 E) : ∃ v : LB.Gen (LB.LinComb t.PP.L
    (rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) rosatiε), v.IsGen := by
  obtain ⟨u, hu⟩ := gen_of_lbIso (LBIso.symm (t.adj a))
  obtain ⟨v, hv, -⟩ := exists_gen t.PP.isLB (φ' := rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) (ε' := rosatiε)
    (fun U _ k => by
      have p := prod_ros (t.act.act a) (t.act.act (H.bar a)) (fst t.G t.G) (snd t.G t.G) k
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      refine (prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := U) _ (prod_cube₂ _ _ k)
        (prod_neg _ _ (prod_cube₂ _ _ k))).trans (Eq.trans ?_ p.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) u hu
  exact ⟨v, hv⟩

theorem rosati_fibre (t : SAB H S) {K : Type} [Field K] (P : PolAV (Sp K)) (x : Sp K ⟶ S)
    {α : P.A.left ⟶ t.G.left} (hα : IsGrpPullback P.A t.G x α) (hL : LBIso P.L (t.PP.L.pull α))
    {a b : P.A ⟶ P.A} (c : 𝓞 E) (ha : a.left ≫ α = α ≫ (t.act.act c).left)
    (hb : b.left ≫ α = α ≫ (t.act.act (H.bar c)).left) : RosatiAdj P.A P.L a b := by
  haveI := P.isAb.comm
  let U₂ := lift (pushPt hα.1.w (fst P.A P.A)) (pushPt hα.1.w (snd P.A P.A))
  have u₁ : U₂.left ≫ (fst t.G t.G).left = (fst P.A P.A).left ≫ α := TripleDescent.lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd t.G t.G).left = (snd P.A P.A).left ≫ α := TripleDescent.lift_left_snd _ _
  have v₁ : (fst P.A P.A ≫ a).left ≫ α = U₂.left ≫ (fst t.G t.G ≫ t.act.act c).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, ← u₁, Category.assoc]
  have v₂ : (snd P.A P.A ≫ b).left ≫ α = U₂.left ≫ (snd t.G t.G ≫ t.act.act (H.bar c)).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, ← u₂, Category.assoc]
  have hφ : ∀ k, rosatiφ P.A a b k ≫ α = U₂.left ≫ rosatiφ t.G (t.act.act c) (t.act.act (H.bar c)) k := fun k => by
    fin_cases k
    exacts [ArcPull.mul_push hα U₂.left v₁ u₂.symm, v₁, u₂.symm, ArcPull.mul_push hα U₂.left u₁.symm v₂, u₁.symm, v₂]
  obtain ⟨t₀, ht₀⟩ := sab_gen t c
  obtain ⟨w, hw⟩ := hL
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : LB.Gen (LB.LinComb t.PP.L (fun k => rosatiφ P.A a b k ≫ α) rosatiε), t₁.IsGen := by
    rw [show (fun k => rosatiφ P.A a b k ≫ α) = fun k => U₂.left ≫ rosatiφ t.G (t.act.act c) (t.act.act (H.bar c)) k
      from funext hφ]
    exact ⟨_, DVR.pullGen_isGen _ _ _ t₀ ht₀ _⟩
  obtain ⟨a₀, ha₀⟩ := exists_down ((isGen_iff w).1 hw) t.PP.isLB P.isLB t₁ ht₁
  exact fun s => ⟨⊤, trivial, _, DVR.pullGen_isGen _ _ _ a₀ ha₀ _⟩

theorem exists_oact (t : SAB H S) {K : Type} [Field K] (P : PolAV (Sp K)) (x : Sp K ⟶ S)
    {α : P.A.left ⟶ t.G.left} (hα : IsGrpPullback P.A t.G x α) (hL : LBIso P.L (t.PP.L.pull α)) :
    letI := H.starRing
    ∃ ρ : P.OAct (𝓞 E), ∀ c, (ρ.act c).left ≫ α = α ≫ (t.act.act c).left := by
  letI := H.starRing
  haveI := P.isAb.comm
  obtain ⟨β, hβm, hβ⟩ := grpPullback_iso (isGrpPullback_pullback t.G x) hα
  haveI := hβm
  let j' : OAct (𝓞 E) P.A := PolPartPull.oActIso β (OAct.pullback x t.G t.act)
  have hj : ∀ c, (j'.act c).left ≫ α = α ≫ (t.act.act c).left := fun c => by
    show (β.inv ≫ (Over.pullback x).map (t.act.act c) ≫ β.hom).left ≫ α = _
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hβ, PolPartPull.pbMap_fst, ← hβ,
      ← Category.assoc, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
  exact ⟨{ j'.toRingAct with rosati := fun c => rosati_fibre t P x hα hL c (hj c) (hj (star c)) }, hj⟩

end GlobalTheory.UMinQF

noncomputable section
namespace GlobalTheory.UMinQF
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem range_finite {La Q : Type} [AddCommGroup La] [Module.Finite ℤ La] [CommGroup Q] (f : La → Q)
    (hf : ∀ a b, f (a + b) = f a * f b) (n : ℕ) (hn : 0 < n) (hk : ∀ a, f (n • a) = 1) : (Set.range f).Finite := by
  let φ : Multiplicative La →* Q := MonoidHom.mk' (fun a => f a.toAdd) (fun a b => hf _ _)
  haveI : Group.FG (Multiplicative La) := AddGroup.fg_iff_mul_fg.1 (Module.Finite.iff_addGroup_fg.1 ‹_›)
  haveI := Group.fg_range φ
  have hpow : ∀ a : Multiplicative La, φ a ^ n = 1 := fun a => by
    rw [← map_pow]; exact hk a.toAdd
  haveI : Finite φ.range := CommGroup.finite_of_fg_isMulTorsion _ (fun y => by
    obtain ⟨_, a, rfl⟩ := y
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, Subtype.ext (hpow a)⟩)
  have : Set.range f = (φ.range : Set Q) := by
    ext q; constructor
    · rintro ⟨a, rfl⟩; exact ⟨Multiplicative.ofAdd a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨a.toAdd, rfl⟩
  rw [this]; exact Set.toFinite _

theorem tors_finite (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) {K : Type} [Field K] [IsAlgClosed K]
    (P : PolAV (Sp K)) (x : Sp K ⟶ Xo.X) {α : P.A.left ⟶ Xo.univ.t.G.left}
    (hα : IsGrpPullback P.A Xo.univ.t.G x α) (n : ℕ) (hn : 0 < n) :
    {z : baseOver (Sp K) ⟶ P.A | z ^ n = 1}.Finite := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  have hs : x ≫ Xo.s = spMap (Spec.preimage (x ≫ Xo.s)).hom := by simp [spMap]
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x _ hs
  have hR : (Set.range (I.ev n)).Finite := range_finite (I.ev n) (I.add n) n hn (fun a =>
    (I.ker n hn (n • a)).2 ⟨a, rfl⟩)
  let e : Over.mk x ⟶ Over.mk (𝟙 (Sp K) ≫ x) := Over.homMk (𝟙 _) (by simp)
  refine Set.Finite.of_injOn (f := fun z => e ≫ ObjPull.pushEquiv hα (baseOver (Sp K)) z) (t := Set.range (I.ev n))
    (fun z hz => ?_) (fun z _ z' _ h => ?_) hR
  · have : (e ≫ ObjPull.pushEquiv hα (baseOver (Sp K)) z) ^ n = 1 := by
      rw [← MonObj.comp_pow, ← map_pow, show z ^ n = 1 from hz, map_one, MonObj.comp_one]
    exact (I.onto n hn _).1 this
  · apply (ObjPull.pushEquiv hα (baseOver (Sp K))).injective
    apply Over.OverMorphism.ext
    have := congrArg CommaMorphism.left h
    simpa [e] using this

end GlobalTheory.UMinQF

noncomputable section
namespace GlobalTheory.UMinQF

theorem addFun_finite {La Q : Type} [AddCommGroup La] [Module.Finite ℤ La] [CommGroup Q] (T : Set Q) (hT : T.Finite) :
    {f : La → Q | (∀ a b, f (a + b) = f a * f b) ∧ ∀ a, f a ∈ T}.Finite := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := La)
  let hom : ∀ f : La → Q, (∀ a b, f (a + b) = f a * f b) → La →ₗ[ℤ] Additive Q := fun f hf =>
    (AddMonoidHom.mk' (fun a => Additive.ofMul (f a)) (fun a b => by rw [hf]; rfl)).toIntLinearMap
  refine Set.Finite.of_injOn (f := fun f (g : s) => f g) (t := {v : s → Q | ∀ i, v i ∈ T})
    (fun f hf => fun g => hf.2 g) (fun f hf f' hf' h => ?_) (Set.Finite.pi' fun _ => hT)
  have := LinearMap.ext_on hs (f := hom f hf.1) (g := hom f' hf'.1) (fun g hg => by
    show Additive.ofMul (f g) = Additive.ofMul (f' g)
    exact congrArg Additive.ofMul (congrFun h ⟨g, hg⟩))
  funext a
  exact congrArg Additive.toMul (LinearMap.congr_fun this a)

end GlobalTheory.UMinQF

noncomputable section
namespace GlobalTheory.UMinQF

theorem pow_of_add {La Q : Type} [AddCommGroup La] [Group Q] (f : La → Q) (hf : ∀ a b, f (a + b) = f a * f b)
    (n : ℕ) (a : La) : f (n • a) = f a ^ n :=
  (AddMonoidHom.mk' (fun a => Additive.ofMul (f a)) (fun a b => by rw [hf]; rfl)).map_nsmul n a

theorem finite_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (s₀ : Sp K ⟶ Sp (KA l)), Set.Finite {x : Sp K ⟶ Xo.X | x ≫ Xo.s = s₀ ∧ ∃ α : P.A.left ⟶ Xo.univ.t.G.left, IsGrpPullback P.A Xo.univ.t.G x α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α)} := by
  intro E _ _ _ H Dw l Xo K _ _ P s₀
  haveI := P.isAb.comm
  letI := H.starRing
  haveI := Dw.fin
  haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  haveI : CharZero K := charZero_of_injective_ringHom
    (((Spec.preimage s₀).hom.comp (algebraMap ℚ (KA l))).injective)
  set X0 := {x : Sp K ⟶ Xo.X | x ≫ Xo.s = s₀ ∧ ∃ α : P.A.left ⟶ Xo.univ.t.G.left,
    IsGrpPullback P.A Xo.univ.t.G x α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α)} with hX0
  have hx : ∀ x : X0, ∃ (α : P.A.left ⟶ Xo.univ.t.G.left) (_ : IsGrpPullback P.A Xo.univ.t.G x.1 α)
      (_ : LBIso P.L (Xo.univ.t.PP.L.pull α)) (ρ : P.OAct (𝓞 E)),
      ∀ c, (ρ.act c).left ≫ α = α ≫ (Xo.univ.t.act.act c).left := fun x => by
    obtain ⟨-, α, h₁, h₂⟩ := x.2
    obtain ⟨ρ, hρ⟩ := exists_oact Xo.univ.t P x.1 h₁ h₂
    exact ⟨α, h₁, h₂, ρ, hρ⟩
  choose α hα hL ρ hρ using hx
  let pt : ∀ x : X0, (𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) →* (baseOver (Sp K) ⟶ P.A) := fun x => ObjPull.secPull (hα x)
  rcases X0.eq_empty_or_nonempty with h0 | ⟨x₀, hx₀⟩
  · rw [h0]; exact Set.finite_empty
  have hM : 0 < l.M := by have := l.three_le; omega
  have TM := tors_finite Dw l Xo P _ (hα ⟨x₀, hx₀⟩) l.M hM
  have TA := tors_finite Dw l Xo P _ (hα ⟨x₀, hx₀⟩) l.A l.A_pos
  have hMb : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left h
  let F := fun x : X0 => ((fun c => (ρ x).act c), (fun a => pt x (Xo.univ.eta a)), (fun a => pt x (Xo.univ.etaA a)))
  set As := {act : 𝓞 E → (P.A ⟶ P.A) | ∃ ρ : P.OAct (𝓞 E), ∀ a, ρ.act a = act a}
  have hA : As.Finite := GlobalTheory.T.finite_integerRing_actions_principallyPolarised E H K P
  set FM := {f : Dw.La → (baseOver (Sp K) ⟶ P.A) | (∀ a b, f (a + b) = f a * f b) ∧
    ∀ a, f a ∈ {z : baseOver (Sp K) ⟶ P.A | z ^ l.M = 1}}
  set FA := {f : Dw.La → (baseOver (Sp K) ⟶ P.A) | (∀ a b, f (a + b) = f a * f b) ∧
    ∀ a, f a ∈ {z : baseOver (Sp K) ⟶ P.A | z ^ l.A = 1}}
  have hFM : FM.Finite := addFun_finite _ TM
  have hFA : FA.Finite := addFun_finite _ TA
  have mem : ∀ x, F x ∈ As ×ˢ FM ×ˢ FA := fun x => by
    refine ⟨⟨ρ x, fun _ => rfl⟩, ⟨fun a b => ?_, fun a => ?_⟩, ⟨fun a b => ?_, fun a => ?_⟩⟩
    · show pt x _ = pt x _ * pt x _
      rw [Xo.univ.eta_add, map_mul]
    · show pt x _ ^ l.M = 1
      rw [← map_pow, ← pow_of_add _ Xo.univ.eta_add, Xo.univ.eta_ker, map_one]
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul hMb Submodule.mem_top
    · show pt x _ = pt x _ * pt x _
      rw [Xo.univ.etaA_add, map_mul]
    · show pt x _ ^ l.A = 1
      rw [← map_pow, ← pow_of_add _ Xo.univ.etaA_add, Xo.univ.etaA_ker, map_one]
  have inj : Function.Injective F := by
    intro x x' h
    simp only [F, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    apply Subtype.ext
    refine GlobalTheory.T.moduli_geometric_point_eq_of_same_fibre_action_level E H Dw l Xo K P x.1 x'.1 (α x) (α x') (x.2.1.trans x'.2.1.symm) (hα x) (hα x') (hL x) (hL x')
      (fun a => ⟨(ρ x).act a, hρ x a, by rw [congrFun h1 a]; exact hρ x' a⟩)
      (fun a => ⟨pt x (Xo.univ.eta a), ObjPull.secPull_left (hα x) _, by
        rw [congrFun h2 a]; exact ObjPull.secPull_left (hα x') _⟩)
      (fun a => ⟨pt x (Xo.univ.etaA a), ObjPull.secPull_left (hα x) _, by
        rw [congrFun h3 a]; exact ObjPull.secPull_left (hα x') _⟩)
  haveI := (hA.prod (hFM.prod hFA)).to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_injective (fun x => (⟨F x, mem x⟩ : ↥(As ×ˢ FM ×ˢ FA)))
    (fun x x' h => inj (congrArg Subtype.val h)))

end GlobalTheory.UMinQF
