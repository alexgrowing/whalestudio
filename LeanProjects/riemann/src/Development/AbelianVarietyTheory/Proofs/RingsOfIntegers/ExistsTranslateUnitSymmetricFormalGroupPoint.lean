import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpec
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBound
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SurjectiveAppTopIntegralModelSquare
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetFramesDifferByUnitEachOrder
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowerSeriesLimitOfCompatibleJetPointsStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SpecPowerSeriesHomExtOfJetsStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantSectionEqLimitChartPointStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSymmetricLiftOddOrderLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricLiftOrderSymmetryMultiplicativityStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GermSymmetricTranslateFibreEqModelStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvalThetaSeriesMulQuadraticPartialsStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvalIotaSeriesEqQuadraticInversionPartialsStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.PlaceInt.FormalPts GlobalTheory.LinkRel GlobalTheory.FrameBiextId

namespace GlobalTheory.TransUnit

section Alg
variable {Γ Γ' U : Type*} [CommGroup Γ] [CommGroup Γ'] [CommGroup U]

theorem LiftLaws.pull {I : Type*} {U' : I → Type*} [∀ i, CommGroup (U' i)] (P : Γ →* Γ') (g : ∀ i, U →* U' i)
    (hg : ∀ u v, (∀ i, g i u = g i v) → u = v) {θ : Γ → Γ → Γ → U} {ρ φ : Γ → U} {w : Γ → Γ} {w' : Γ' → Γ'}
    {θ' : ∀ i, Γ' → Γ' → Γ' → U' i} {ρ' φ' : ∀ i, Γ' → U' i} (hw : ∀ x, w' (P x) = P (w x))
    (hθ : ∀ i x y z, θ' i (P x) (P y) (P z) = g i (θ x y z)) (hρ : ∀ i x, ρ' i (P x) = g i (ρ x))
    (hφ : ∀ i x, φ' i (P x) = g i (φ x)) {a : Γ} {k : ℕ} (h : ∀ i, LiftLaws (θ' i) (ρ' i) (φ' i) w' (P a) k) :
    LiftLaws θ ρ φ w a k := by
  refine ⟨fun x => hg _ _ fun i => ?_, hg _ _ fun i => ?_, fun x y => hg _ _ fun i => ?_⟩
  · have := (h i).1 (P x)
    simp only [← map_pow P, ← map_mul P, hφ] at this
    rw [map_prod, this, map_one]
  · have := (h i).2.1
    rw [← map_one P, ← map_inv P, hφ, hφ, hρ, hρ, quadN_map P (g i) hw (hθ i) (hθ i)] at this
    simp only [map_mul, map_pow, map_div, map_one]
    exact this
  · have := (h i).2.2 (P x) (P y)
    rw [← map_one P, ← map_mul P, hφ, hφ, hφ, hφ, hρ, map_lineCoeffCubic P (g i) (hρ i),
      quadQ_map P (g i) hw (hθ i) (hθ i)] at this
    simp only [map_mul, map_pow, map_div]
    exact this

def trU (ρ φ : Γ → U) (e : Γ → Γ → U) (w : Γ → Γ) (a : Γ) (k : ℕ) (x : Γ) : U :=
  φ x * (ρ (a * x) * e (a * x) (w (a * x)) / (ρ x * e x (w x))) ^ k

theorem trU_laws {θ p₁ p₂ : Γ → Γ → Γ → U} {ρ φ : Γ → U} {e : Γ → Γ → U} (w : Γ →* Γ) {a : Γ} {k : ℕ}
    (h : LiftLaws θ ρ φ w a k) (ha : a ^ k = 1)
    (h₁ : ∀ x y z, θ x y z = p₁ x y z * (e (x * y) z / (e x z * e y z)))
    (h₂ : ∀ x y z, θ x y z = p₂ x y z * (e x (y * z) / (e x y * e x z)))
    (e₁ : ∀ z, e 1 z = 1) (e₂ : ∀ x, e x 1 = 1) :
    (∀ x y, trU ρ φ e w a k (x * y) * trU ρ φ e w a k 1 =
      trU ρ φ e w a k x * trU ρ φ e w a k y * (quadQ p₁ p₂ w x y a)⁻¹ ^ k) ∧
    (∀ x, ∏ j ∈ Finset.range k, trU ρ φ e w a k (a ^ j * x) = 1) ∧
    trU ρ φ e w a k 1 * quadN p₁ p₂ w a ^ k * trU ρ φ e w a k a⁻¹ = 1 := by
  obtain ⟨o, s, m⟩ := h
  refine ⟨fun x y => ?_, fun x => ?_, ?_⟩
  · have := congrArg Additive.ofMul (m x y)
    rw [quadQ_of_diff w h₁ h₂] at this
    apply Additive.ofMul.injective
    simp only [trU, c3, _root_.mul_one, _root_.one_mul, e₁, mul_comm a, ofMul_mul, ofMul_div, ofMul_pow, ofMul_inv, ofMul_one] at this ⊢
    linear_combination (norm := module) this
  · simp only [trU]
    rw [Finset.prod_mul_distrib, o, _root_.one_mul, Finset.prod_pow]
    have := Finset.prod_range_div (fun j => ρ (a ^ j * x) * e (a ^ j * x) (w (a ^ j * x))) k
    simp only [pow_succ', _root_.mul_assoc] at this
    rw [this, ha, pow_zero, div_self', one_pow]
  · have := congrArg Additive.ofMul s
    rw [quadN_of_diff w h₁ h₂ e₁ e₂] at this
    apply Additive.ofMul.injective
    simp only [trU, _root_.mul_one, mul_inv_cancel, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at this ⊢
    linear_combination (norm := module) this

end Alg

section Read
variable {A : Type} [CommRing A]

def cstH (z : Sp A) : A →+* (Sp A).presheaf.stalk z := ((Sp A).presheaf.germ ⊤ z trivial).hom.comp (toΓ A)

theorem cstH_eq (z : Sp A) (a : A) : cstH z a = cst (𝟙 _) z a := (gs_eq (𝟙 _) z ⊤ trivial _).symm

def gu (z : Sp A) : Aˣ →* ((Sp A).presheaf.stalk z)ˣ := Units.map (cstH z : A →* _)

theorem cstH_ext {a b : A} (h : ∀ z, cstH z a = cstH z b) : a = b :=
  H1.cst_ext fun z => (cstH_eq z a).symm.trans ((h z).trans (cstH_eq z b))

variable {X Y : Scheme.{0}} {L : LB X} {j : L.ι} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem top_le_wchart (r : Sp A ⟶ Y) (h : ∀ k, ⊤ ≤ (r ≫ φ k) ⁻¹ᵁ L.U j) :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j) := fun _ _ => Set.mem_iInter.2 fun k => h k trivial

theorem gs_read (r : Sp A ⟶ Y) (W : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ W) (f : Γ(Y, W)) {A' : Type} [CommRing A'] (ψ : A →+* A')
    (z : Sp A') : gs (spMap ψ ≫ r) z W f = cstH z (ψ (JetSer.fnValHom r W h f)) := by
  rw [← JetSer.fnVal_eq_fnValHom, ← JetSer.fnVal_specMap ψ r W h]
  exact (JetSer.valSer_germ_fnVal _ _ (JetSer.top_le_preimage_comp _ r W h) z _).symm

theorem exists_read_sec (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp A ⟶ Y) (h : ∀ k, ⊤ ≤ (r ≫ φ k) ⁻¹ᵁ L.U j) :
    ∃ u : A, ∀ (A' : Type) [CommRing A'] (ψ : A →+* A') (z : Sp A') (J), Pref L j z J →
      sval s (spMap ψ ≫ r) z J = cstH z (ψ u) := by
  have h' := top_le_wchart r h
  refine ⟨_, fun A' _ ψ z J hJ => Eq.trans ?_ (gs_read r _ h' (s.f fun _ => j) ψ z)⟩
  exact sval_of s _ z J (fun _ => j) fun k =>
    hJ.2 _ (Set.mem_iInter.1 (JetSer.top_le_preimage_comp (spMap ψ) r _ h' (show z ∈ ⊤ from trivial)) k)

theorem exists_read_gen (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp A ⟶ Y) (h : ∀ k, ⊤ ≤ (r ≫ φ k) ⁻¹ᵁ L.U j) :
    ∃ u : Aˣ, ∀ (A' : Type) [CommRing A'] (ψ : A →+* A') (z : Sp A') (J), Pref L j z J →
      val t (spMap ψ ≫ r) z J = gu z (Units.map (ψ : A →* A') u) := by
  have h' := top_le_wchart r h
  refine ⟨Units.map (JetSer.fnValHom r _ h').toMonoidHom (t.s fun _ => j), fun A' _ ψ z J hJ => Units.ext ?_⟩
  exact (val_pref hJ t _ (JetSer.top_le_preimage_comp (spMap ψ) r _ h' (show z ∈ ⊤ from trivial))).trans
    (gs_read r _ h' _ ψ z)

end Read

section Model
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {B : FB V d (𝓞 E)}
  {k n : ℕ}

variable (B) in

def toSm (u : Q V d n) : Sm B n := ⟨u.1, fun i => by rw [u.2 i]; exact zero_mem _⟩

theorem evA_toSm (b : Fin k → Q V d n) (f : PS V k d) : evA (fun j => toSm B (b j)) f = sb b f :=
  (evA_eq_ev (fun j => toSm B (b j)) (fun j i => (b j).2 i) f).trans (sb_apply b f).symm

theorem toSm_op (u v : Q V d n) : toSm B (op (FQ B.G) u v) = toSm B u * toSm B v :=
  Subtype.ext (funext fun i => (evA_toSm (B := B) ![u, v] (B.G.F i)).symm.trans
    ((congrArg (evA · (B.G.F i)) (funext fun j => by fin_cases j <;> rfl)).trans (smallPointsSubstitutionAlgHom_two_points _ _ _)))

theorem toSm_ac (o : 𝓞 E) (u : Q V d n) : toSm B (ac (AQ B.A o) u) = Sm.act B o (toSm B u) :=
  Subtype.ext (funext fun i => (evA_toSm (B := B) ![u] (B.A.act o i)).symm.trans
    ((congrArg (evA · (B.A.act o i)) (funext fun j => by fin_cases j; rfl)).trans (smallPointsSubstitutionAlgHom_single_point _ _)))

theorem jetA_evA (m : ℕ) (b : Fin k → Q V d n) :
    (jetA _ m).comp (evA fun j => toSm B (b j)) = (jQ m b).comp (jetA _ m) :=
  AlgHom.ext fun f => (congrArg (psJet m) (evA_toSm b f)).trans (jQ_psJet m b f).symm

variable {t : SAB H (Sp V)} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {X : limO V d 1 ⟶ t.G} (hX : IsLimit x X)

include hX in
theorem jet_ptOf (m : ℕ) (u : Q V d n) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetA _ m) ≫ ptOf X (toSm B u) = PP m x u := by
  have e : (![toSm B u] : Fin 1 → Sm B n) = fun j => toSm B (![u] j) := funext fun j => by fin_cases j; rfl
  rw [ptOf, PP, ← hX m, ← Category.assoc, ← Category.assoc, GermD.homAt_comp, GermD.homAt_comp, e, jetA_evA]

theorem lim_ext {p q : limO V d n ⟶ t.G}
    (h : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetA _ m) ≫ p = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetA _ m) ≫ q) : p = q :=
  Over.OverMorphism.ext (GlobalTheory.T.spec_powerSeries_hom_ext_of_jets V _ _ _ _ fun m => congrArg (fun r => r.left) (h m))

variable {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber V) ⟶ t.G.left)} {uvec : κ → Fin d → V}
  (hc : IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uvec x)

include hX hc

theorem ptOf_mul (a b : Sm B n) : ptOf X (a * b) = ptOf X a * ptOf X b := by
  have h : ptOf X (toSm B (gen 0 : Q V d 2) * toSm B (gen 1)) = ptOf X (toSm B (gen 0)) * ptOf X (toSm B (gen 1)) :=
    lim_ext fun m => by
      rw [MonObj.comp_mul, ← toSm_op, jet_ptOf hX, jet_ptOf hX, jet_ptOf hX, PP_op hc]
  have := congrArg (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (evA ![a, b]) ≫ ·) h
  simp only [MonObj.comp_mul, ptOf_sub, map_mul] at this
  rwa [show Sm.sub ![a, b] (toSm B (gen 0)) = a from Sm.sub_gen _ 0,
    show Sm.sub ![a, b] (toSm B (gen 1)) = b from Sm.sub_gen _ 1] at this

theorem ptOf_act (o : 𝓞 E) (a : Sm B n) : ptOf X (Sm.act B o a) = ptOf X a ≫ t.act.act o := by
  have h : ptOf X (Sm.act B o (toSm B (gen 0 : Q V d 1))) = ptOf X (toSm B (gen 0)) ≫ t.act.act o :=
    lim_ext fun m => by
      rw [← Category.assoc, ← toSm_ac, jet_ptOf hX, jet_ptOf hX, PP_ac hc]
  have := congrArg (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (evA ![a]) ≫ ·) h
  simp only [← Category.assoc, ptOf_sub, Sm.sub_act] at this
  rwa [show Sm.sub ![a] (toSm B (gen 0)) = a from Sm.sub_gen _ 0] at this

def ptH (n : ℕ) : Sm B n →* (limO V d n ⟶ t.G) := MonoidHom.mk' (ptOf X) (ptOf_mul hX hc)

omit hX hc in
theorem ptOf_gen : ptOf X (Sm.gen B 0) = X := by
  have e : evA ![(Sm.gen B 0 : Sm B 1)] = AlgHom.id V _ := AlgHom.ext fun f =>
    (congrArg (evA · f) (funext fun j => by fin_cases j; rfl)).trans (evA_gen f)
  rw [ptOf, e, GermD.homAt_id, Category.id_comp]

theorem lim_mem (W : t.G.left.Opens) (hW : ⊤ ≤ η[t.G].left ⁻¹ᵁ W) : ⊤ ≤ X.left ⁻¹ᵁ W := by
  let χ : PS V 1 d →ₐ[V] V := (jetAug : Jet V _ 0 →ₐ[V] V).comp (jetA _ 0)
  have hs : Function.Surjective (χ : PS V 1 d →+* V) := fun a => ⟨algebraMap V _ a, χ.commutes a⟩
  have e : Formalism.L2.Pj.homAt (𝟙 (Sp V)) χ ≫ X = 1 := by
    rw [← GermD.homAt_comp, Category.assoc, hX 0, hc.zero 0]
  have e' : spMap (χ : PS V 1 d →+* V) ≫ X.left = (toUnit (overAt (𝟙 (Sp V)) V)).left ≫ η[t.G].left :=
    congrArg (fun q => q.left) e
  have : IsLocalHom (CommRingCat.ofHom (χ : PS V 1 d →+* V)).hom := IsLocalHom.of_surjective _ hs
  have h : ((toUnit (overAt (𝟙 (Sp V)) V)).left ≫ η[t.G].left) (closedPoint V) ∈ W := hW trivial
  rw [← e'] at h
  have h2 : spMap (χ : PS V 1 d →+* V) (closedPoint V) = closedPoint (PS V 1 d) := Spec_closedPoint
  have h3 : closedPoint (PS V 1 d) ∈ (X.left ⁻¹ᵁ W : (Sp (PS V 1 d)).Opens) := by rw [← h2]; exact h
  exact ((IsLocalRing.closedPoint_mem_iff _).1 h3).ge

theorem range_mem (W : t.G.left.Opens) (hW : ⊤ ≤ η[t.G].left ⁻¹ᵁ W) {p : limO V d n ⟶ t.G}
    (hp : p ∈ (ptH hX hc n).range) : ⊤ ≤ p.left ⁻¹ᵁ W := by
  obtain ⟨a, rfl⟩ := hp
  exact JetSer.top_le_preimage_comp _ X.left W (lim_mem hX hc W hW)

theorem psum_mem {T : Over (Sp V)} {l : ℕ} (r : limO V d n ⟶ T) (xs : Fin l → (T ⟶ t.G))
    (h : ∀ i, r ≫ xs i ∈ (ptH hX hc n).range) (I : Finset (Fin l)) : r ≫ psum t.G xs I ∈ (ptH hX hc n).range := by
  unfold psum
  induction (List.finRange l).filter (· ∈ I) with
  | nil => exact (congrArg (· ∈ (ptH hX hc n).range) (MonObj.comp_one r)).mpr (one_mem _)
  | cons a s ih => exact (congrArg (· ∈ (ptH hX hc n).range) (MonObj.comp_mul r _ _)).mpr (mul_mem (h a) ih)

theorem range_mem' (W : t.G.left.Opens) (hW : ⊤ ≤ η[t.G].left ⁻¹ᵁ W) {p : limO V d n ⟶ t.G}
    (hp : p ∈ (ptH hX hc n).range) {q : Sp (PS V n d) ⟶ t.G.left} (e : q = p.left) : ⊤ ≤ q ⁻¹ᵁ W :=
  e ▸ range_mem hX hc W hW hp

def toBase (T : Over (Sp V)) : T ⟶ baseOver (Sp V) := Over.homMk T.hom (Category.comp_id _)

omit hX hc [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem base_ext {T : Over (Sp V)} (f g : T ⟶ baseOver (Sp V)) : f = g :=
  Over.OverMorphism.ext (((Category.comp_id _).symm.trans (Over.w f)).trans
    ((Category.comp_id _).symm.trans (Over.w g)).symm)

variable {j : t.PP.L.ι} (hj : ⊤ ≤ η[t.G].left ⁻¹ᵁ t.PP.L.U j)
include hj

theorem read_prim (wP : PrimTyG t) : ∃ ρ : (PS V 1 d)ˣ, ∀ (n : ℕ) (A : Type) [CommRing A] [Algebra V A]
    (ψ : PS V n d →ₐ[V] A) (z : Sp A) (J), Pref t.PP.L j z J → ∀ a : Sm B n,
      val wP (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X a).left z J = gu z (Units.map (ψ : PS V n d →* A) (u1 ρ a)) := by
  have g : X ∈ (ptH hX hc 1).range := ⟨Sm.gen B 0, ptOf_gen⟩
  obtain ⟨ρ, hρ⟩ := exists_read_gen (j := j) wP X.left (by
    rintro (i | I)
    · exact range_mem' hX hc _ hj g (Category.comp_id _)
    · refine range_mem' hX hc _ hj (psum_mem hX hc X ![𝟙 t.G, t.act.act H.w0] (fun i => ?_) I.down) (Over.comp_left _ _ _ _ _).symm
      fin_cases i
      · exact (congrArg (· ∈ (ptH hX hc 1).range) (Category.comp_id X)).mpr g
      · exact ⟨Sm.act B H.w0 (Sm.gen B 0), (ptOf_act hX hc _ _).trans (by rw [ptOf_gen]; rfl)⟩)
  refine ⟨ρ, fun n A _ _ ψ z J hJ a => Eq.trans ?_ (hρ A (ψ.comp (evA ![a])) z J hJ)⟩
  rw [ptOf, ← Category.assoc, GermD.homAt_comp]
  rfl

theorem read_cub : ∃ θ : (PS V 3 d)ˣ, ∀ (n : ℕ) (A : Type) [CommRing A] [Algebra V A]
    (ψ : PS V n d →ₐ[V] A) (z : Sp A) (J), Pref t.PP.L j z J → ∀ a b c : Sm B n,
      cubV t.cub (T := overAt (𝟙 (Sp V)) A) z J (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X a)
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X b) (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X c) =
        gu z (Units.map (ψ : PS V n d →* A) (u3 θ a b c)) := by
  obtain ⟨θ, hθ⟩ := exists_read_gen (j := j) (φ := thφ t.G (x3 t.G)) (ε := thε) t.cub.t
    (lift (ptOf X (Sm.gen B (0 : Fin 3))) (lift (ptOf X (Sm.gen B 1)) (ptOf X (Sm.gen B 2)))).left (fun I => by
      refine range_mem' hX hc _ hj (psum_mem hX hc _ (x3 t.G) (fun i => ?_) I.down) (Over.comp_left _ _ _ _ _).symm
      fin_cases i
      · exact ⟨Sm.gen B 0, by simp [x3]; rfl⟩
      · exact ⟨Sm.gen B 1, by simp [x3]; rfl⟩
      · exact ⟨Sm.gen B 2, by simp [x3]; rfl⟩)
  refine ⟨θ, fun n A _ _ ψ z J hJ a b c => Eq.trans ?_ (hθ A (ψ.comp (evA ![a, b, c])) z J hJ)⟩
  have e : lift (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X a) (lift (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X b)
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X c)) = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (ψ.comp (evA ![a, b, c])) ≫
      lift (ptOf X (Sm.gen B (0 : Fin 3))) (lift (ptOf X (Sm.gen B 1)) (ptOf X (Sm.gen B 2))) := by
    simp only [← GermD.homAt_comp, comp_lift, Category.assoc, ptOf_sub, Sm.sub_gen]
    rfl
  rw [cubV, e]
  rfl

omit hX hc hj in
theorem lift_base {A : Type} [CommRing A] [Algebra V A] (ψ : PS V n d →ₐ[V] A) (a : Sm B n)
    (σ : overAt (𝟙 (Sp V)) A ⟶ baseOver (Sp V)) :
    (lift σ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X a)).left =
      spMap (ψ.comp (evA ![a]) : PS V 1 d →+* A) ≫ (lift (toBase _) X).left := by
  have e : lift σ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X a) =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (ψ.comp (evA ![a])) ≫ lift (toBase _) X := by
    rw [comp_lift, ptOf, ← Category.assoc, GermD.homAt_comp, base_ext σ]
  rw [e]
  rfl

theorem read_sec {k : ℤ} (s : LB.Sec (LPow t.G t.PP.L k (baseOver (Sp V)))) :
    ∃ S : PS V 1 d, ∀ (n : ℕ) (A : Type) [CommRing A] [Algebra V A]
    (ψ : PS V n d →ₐ[V] A) (z : Sp A) (J), Pref t.PP.L j z J → ∀ (a : Sm B n) (σ : overAt (𝟙 (Sp V)) A ⟶ baseOver (Sp V)),
      RegularGerm.sv t s (lift σ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X a)).left z J = cstH z (ψ (evA ![a] S)) := by
  obtain ⟨S, hS⟩ := exists_read_sec (j := j) (φ := fun _ : Fin 1 => (snd (baseOver (Sp V)) t.G).left) (ε := fun _ => k) s
    (lift (toBase _) X).left (fun _ => range_mem hX hc _ hj (p := lift (toBase _) X ≫ snd _ _)
      ⟨Sm.gen B 0, ptOf_gen.trans (lift_snd _ _).symm⟩)
  refine ⟨S, fun n A _ _ ψ z J hJ a σ => Eq.trans ?_ (hS A (ψ.comp (evA ![a])) z J hJ)⟩
  rw [lift_base]

theorem read_lift {k : ℤ} (U : ThetaGrp t.G t.PP.L k (baseOver (Sp V))) (a₁ : Sm B 1)
    (ha : toBase _ ≫ U.pt = ptOf X a₁) :
    ∃ φ : (PS V 1 d)ˣ, ∀ (n : ℕ) (A : Type) [CommRing A] [Algebra V A]
    (ψ : PS V n d →ₐ[V] A) (z : Sp A) (J), Pref t.PP.L j z J → ∀ (a : Sm B n) (σ : overAt (𝟙 (Sp V)) A ⟶ baseOver (Sp V)),
      CommPairing.tval U (lift σ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X a)).left z J =
        gu z (Units.map (ψ : PS V n d →* A) (u1 φ a)) := by
  have g : X ∈ (ptH hX hc 1).range := ⟨Sm.gen B 0, ptOf_gen⟩
  obtain ⟨φ, hφ⟩ := exists_read_gen (j := j)
    (φ := ![(snd (baseOver (Sp V)) t.G).left, (translPt t.G U.pt).left]) (ε := ![k, -k]) U.φ
    (lift (toBase _) X).left (fun i => by
      fin_cases i
      · exact range_mem hX hc _ hj (p := lift (toBase _) X ≫ snd _ _) ⟨Sm.gen B 0, ptOf_gen.trans (lift_snd _ _).symm⟩
      · refine range_mem hX hc _ hj (p := lift (toBase _) X ≫ translPt t.G U.pt) ?_
        have e : lift (toBase _) X ≫ translPt t.G U.pt = (toBase _ ≫ U.pt) * X := by
          rw [translPt, comp_lift_assoc, lift_fst_assoc, lift_snd]; rfl
        rw [e, ha]
        exact mul_mem ⟨a₁, rfl⟩ g)
  refine ⟨φ, fun n A _ _ ψ z J hJ a σ => Eq.trans ?_ (hφ A (ψ.comp (evA ![a])) z J hJ)⟩
  rw [lift_base]
  rfl

variable {e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m} {ε₀ : PS V 2 d} (hε : PowGerm.IsEps t x e j ε₀)
include hε

omit hX in
theorem isUnit_eps : IsUnit ε₀ := by
  obtain ⟨u, hu⟩ := exists_read_gen (j := j)
    (φ := cφG t ![jptG t (𝟙 (Sp V)) d x 0 (0 : Fin 2), jptG t (𝟙 (Sp V)) d x 0 (1 : Fin 2)]) (ε := cε 2) (e 0)
    (𝟙 (Sp (Jet V (Fin 2 × Fin d) 0))) (fun I y _ => Set.mem_iInter.1 (mem_frame hc.zero hj 0 y) I)
  have h : psJet 0 ε₀ = u.val := cstH_ext fun z => by
    obtain ⟨J, hJ⟩ := exists_pref t.PP.L j t.PP.isLB (Z := Sp (Jet V (Fin 2 × Fin d) 0)) z
    have a := hu _ (RingHom.id _) z J hJ
    have i : spMap (RingHom.id (Jet V (Fin 2 × Fin d) 0)) = 𝟙 _ := Spec.map_id _
    rw [i, Category.id_comp] at a
    have b := hε 0 z J hJ.1 (fun I => hJ.2 _ (Set.mem_iInter.1 (mem_frame hc.zero hj 0 z) I))
    exact (cstH_eq z _).trans (b.symm.trans (congrArg Units.val a))
  let χ : PS V 2 d →ₐ[V] V := (jetAug : Jet V _ 0 →ₐ[V] V).comp (jetA _ 0)
  have hs : Function.Surjective (χ : PS V 2 d →+* V) := fun a => ⟨algebraMap V _ a, χ.commutes a⟩
  have : IsLocalHom (χ : PS V 2 d →+* V) := IsLocalHom.of_surjective _ hs
  refine isUnit_of_map_unit (χ : PS V 2 d →+* V) _ ?_
  show IsUnit (jetAug (psJet 0 ε₀))
  rw [h]
  exact u.isUnit.map _

omit hX hc hj hε in
theorem VV_eq (m : ℕ) (y : (jOG (𝟙 (Sp V)) d m n).left) (f : PS V n d) :
    VV m y f = cstH (A := Jet V (Fin n × Fin d) m) y (jetA _ m f) := (cstH_eq _ _).symm

omit hX hc hj hε in
theorem unitSeriesValueTwoPoints_smallPoints (f : (PS V 2 d)ˣ) (u v : Q V d n) : (u2 f (toSm B u) (toSm B v)).val = E2 f.val u v :=
  (congrArg (evA · f.val) (funext fun j => by fin_cases j <;> rfl)).trans (evA_toSm (B := B) ![u, v] f.val)

omit hX hc hj hε in
theorem unitSeriesValueThreePoints_smallPoints (f : (PS V 3 d)ˣ) (u v w : Q V d n) : (u3 f (toSm B u) (toSm B v) (toSm B w)).val = E3 f.val u v w :=
  (congrArg (evA · f.val) (funext fun j => by fin_cases j <;> rfl)).trans (evA_toSm (B := B) ![u, v, w] f.val)

omit hX in
theorem ee_gu {ε : (PS V 2 d)ˣ} (h : ε.val = ε₀) {m : ℕ} {y : (jOG (𝟙 (Sp V)) d m n).left} {J}
    (hJ : Pref t.PP.L j y J) (u v : Q V d n) : ee x e y J u v =
      gu (A := Jet V (Fin n × Fin d) m) y (Units.map (jetA (V := V) (Fin n × Fin d) m : PS V n d →* _) (u2 ε (toSm B u) (toSm B v))) :=
  Units.ext ((ee_eps hc.zero hj hε hJ u v).symm.trans ((VV_eq m y _).trans (by rw [← h, ← unitSeriesValueTwoPoints_smallPoints (B := B)]; rfl)))

omit hX hc hj hε in
theorem unit_ext_jets (j : t.PP.L.ι) {f g : (PS V n d)ˣ}
    (h : ∀ m (y : (jOG (𝟙 (Sp V)) d m n).left) J, Pref t.PP.L j y J →
      gu (A := Jet V (Fin n × Fin d) m) y (Units.map (jetA (V := V) (Fin n × Fin d) m : PS V n d →* _) f) =
      gu (A := Jet V (Fin n × Fin d) m) y (Units.map (jetA (V := V) (Fin n × Fin d) m : PS V n d →* _) g)) : f = g :=
  Units.ext (VV_ext_pref j fun m y J hJ =>
    (VV_eq m y _).trans ((congrArg Units.val (h m y J hJ)).trans (VV_eq m y _).symm))

theorem cub_diff (hf : IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e) {ε : (PS V 2 d)ˣ}
    (h : ε.val = ε₀) {θ p₁ p₂ : (PS V 3 d)ˣ} (h₁ : p₁.val = B.ph1) (h₂ : p₂.val = B.ph2)
    (hθ : ∀ (n : ℕ) (A : Type) [CommRing A] [Algebra V A]
      (ψ : PS V n d →ₐ[V] A) (z : Sp A) (J), Pref t.PP.L j z J → ∀ a b c : Sm B n,
      cubV t.cub (T := overAt (𝟙 (Sp V)) A) z J (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X a)
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X b) (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X c) =
        gu z (Units.map (ψ : PS V n d →* A) (u3 θ a b c))) (a b c : Sm B n) :
    u3 θ a b c = u3 p₁ a b c * (u2 ε (a * b) c / (u2 ε a c * u2 ε b c)) ∧
    u3 θ a b c = u3 p₂ a b c * (u2 ε a (b * c) / (u2 ε a b * u2 ε a c)) := by
  let g : Fin 3 → Sm B 3 := fun i => toSm B (gen i)
  have r : u3 θ (g 0) (g 1) (g 2) = u3 p₁ (g 0) (g 1) (g 2) * (u2 ε (g 0 * g 1) (g 2) / (u2 ε (g 0) (g 2) * u2 ε (g 1) (g 2))) ∧
      u3 θ (g 0) (g 1) (g 2) = u3 p₂ (g 0) (g 1) (g 2) * (u2 ε (g 0) (g 1 * g 2) / (u2 ε (g 0) (g 1) * u2 ε (g 0) (g 2))) := by
    refine ⟨unit_ext_jets j fun m y J hJ => ?_, unit_ext_jets j fun m y J hJ => ?_⟩
    · have q := frame_biext_dictionary_first_partial_law hJ.1 hf (gen 0 : Q V d 3) (gen 1) (gen 2)
      have c := hθ 3 _ (jetA _ m) y J hJ (g 0) (g 1) (g 2)
      simp only [g, jet_ptOf hX] at c
      rw [VV_eq, ← h₁, ← unitSeriesValueThreePoints_smallPoints (B := B), c, ee_gu hc hj hε h hJ, ee_gu hc hj hε h hJ, ee_gu hc hj hε h hJ,
        toSm_op] at q
      have q' : gu (A := Jet V (Fin 3 × Fin d) m) y (Units.map (jetA (V := V) (Fin 3 × Fin d) m : PS V 3 d →* _) (u3 p₁ (g 0) (g 1) (g 2))) = _ :=
        Units.ext q
      simp only [map_mul, map_div, q', g]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv]
      abel
    · have q := frame_biext_dictionary_second_partial_law hJ.1 hf (gen 0 : Q V d 3) (gen 1) (gen 2)
      have c := hθ 3 _ (jetA _ m) y J hJ (g 0) (g 1) (g 2)
      simp only [g, jet_ptOf hX] at c
      rw [VV_eq, ← h₂, ← unitSeriesValueThreePoints_smallPoints (B := B), c, ee_gu hc hj hε h hJ, ee_gu hc hj hε h hJ, ee_gu hc hj hε h hJ,
        toSm_op] at q
      have q' : gu (A := Jet V (Fin 3 × Fin d) m) y (Units.map (jetA (V := V) (Fin 3 × Fin d) m : PS V 3 d →* _) (u3 p₂ (g 0) (g 1) (g 2))) = _ :=
        Units.ext q
      simp only [map_mul, map_div, q', g]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv]
      abel
  have s : ∀ i, Sm.sub ![a, b, c] (g i) = ![a, b, c] i := Sm.sub_gen _
  have r₁ := congrArg (evU ![a, b, c]) r.1
  have r₂ := congrArg (evU ![a, b, c]) r.2
  simp only [map_mul (evU _), map_div (evU _), ← unitSeriesValueThreePoints_substitution, ← unitSeriesValueTwoPoints_substitution, map_mul (Sm.sub _), s] at r₁ r₂
  exact ⟨r₁, r₂⟩

theorem germ_read {ε : (PS V 2 d)ˣ} (h : ε.val = ε₀) {wP : PrimTyG t} {ρ : (PS V 1 d)ˣ}
    (hρ : ∀ (n : ℕ) (A : Type) [CommRing A] [Algebra V A]
      (ψ : PS V n d →ₐ[V] A) (z : Sp A) (J), Pref t.PP.L j z J → ∀ a : Sm B n,
      val wP (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X a).left z J = gu z (Units.map (ψ : PS V n d →* A) (u1 ρ a)))
    {k : ℕ} {s : LB.Sec (LPow t.G t.PP.L (k : ℤ) (baseOver (Sp V)))} {S f : PS V 1 d}
    (hS : ∀ (n : ℕ) (A : Type) [CommRing A] [Algebra V A]
      (ψ : PS V n d →ₐ[V] A) (z : Sp A) (J), Pref t.PP.L j z J → ∀ (a : Sm B n) (σ : overAt (𝟙 (Sp V)) A ⟶ baseOver (Sp V)),
      RegularGerm.sv t s (lift σ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ ptOf X a)).left z J = cstH z (ψ (evA ![a] S)))
    (hg : IsGermG t (𝟙 (Sp V)) d x B.A.act e wP k s f) :
    S = f * ((u1 ρ (Sm.gen B 0) * u2 ε (Sm.gen B 0) (Sm.act B H.w0 (Sm.gen B 0))) ^ k).val := by
  have id1 : ∀ f : PS V 1 d, evA ![(Sm.gen B 0 : Sm B 1)] f = f := fun f =>
    (congrArg (evA · f) (funext fun j => by fin_cases j; rfl)).trans (evA_gen f)
  refine VV_ext_pref j fun m y J hJ => ?_
  have q := RegularGerm.sv_of_isGerm hg m (𝟙 _) y hJ.1
  have a := hS 1 _ (jetA _ m) y J hJ (Sm.gen B 0) (jBaseG (𝟙 (Sp V)) d m 1)
  have b := hρ 1 _ (jetA _ m) y J hJ (Sm.gen B 0)
  rw [ptOf_gen, hX m] at a b
  rw [id1] at a
  have i : 𝟙 _ ≫ RegularGerm.jetPt (x m) = (lift (jBaseG (𝟙 (Sp V)) d m 1) (x m)).left := by
    rw [Category.id_comp, RegularGerm.jetPt, ← Over.comp_left, ptSecT, lift_whiskerRight, Category.id_comp]
  have i0 : (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jQ m (gen : Fin 1 → Q V d 1))).left = 𝟙 _ := by
    have : jQ m (gen : Fin 1 → Q V d 1) = AlgHom.id V _ := GermD.jet_hom_ext fun p => (jQ_X m _ p).trans (psJet_X m p)
    rw [this, GermD.homAt_id, Over.id_left]
  have c := val_peG x hJ.1 e (gen : Fin 1 → Q V d 1)
    ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (B.A.act H.w0 j)] (gen 0) (ac (AQ B.A H.w0) (gen 0))
    (by rintro ⟨l, j⟩; fin_cases l; exacts [FrameBiextId.hX 0 j, hA _ 0 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [MvPolynomial.constantCoeff_X _ _, (FBIdPh.cc_psIn d m _ _).trans (B.A.const _ j)])
  rw [i0, sq_ac, sq_gen, ee_gu hc hj hε h hJ, toSm_ac] at c
  have v : val (eLG t (𝟙 (Sp V)) d x B.A.act e wP m) (𝟙 _) y J = gu (A := Jet V (Fin 1 × Fin d) m) y
      (Units.map (jetA (V := V) (Fin 1 × Fin d) m : PS V 1 d →* _) (u1 ρ (Sm.gen B 0) * u2 ε (Sm.gen B 0) (Sm.act B H.w0 (Sm.gen B 0)))) := by
    rw [map_mul, map_mul]
    refine (val_mul hJ.1 _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ.1 _ _ _).trans ?_) c)
    rw [Category.id_comp]
    exact b
  rw [i, v, ← map_pow, ← map_pow] at q
  rw [VV_mul, VV_eq, ← a, q, VV_eq m y (Units.val _)]
  rfl

omit hX hc hj hε in
theorem evA_one (f : PS V 1 d) : evA ![(1 : Sm B n)] f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
  rw [evA_apply]
  refine evC_eq_algHom _ (fun p => (![(1 : Sm B n)] p.1).2 p.2) ((Algebra.ofId V (PS V n d)).comp
    { (MvPowerSeries.constantCoeff : PS V 1 d →+* V) with commutes' := fun c => MvPowerSeries.constantCoeff_C c })
    (fun p => ?_) f
  obtain ⟨i, l⟩ := p
  fin_cases i
  exact (congrArg (Algebra.ofId V (PS V n d)) (MvPowerSeries.constantCoeff_X _)).trans (map_zero _)

omit hX hc hj hε in
theorem exists_unit_ph : (∃ p : (PS V 3 d)ˣ, p.val = B.ph1 ∧ ∀ (n : ℕ) (y z : Sm B n), u3 p 1 y z = 1) ∧
    ∃ p : (PS V 3 d)ˣ, p.val = B.ph2 ∧ ∀ (n : ℕ) (y z : Sm B n), u3 p y 1 z = 1 := by
  have un : ∀ (f : PS V 3 d) (b : Fin 3 → Pt V 2 d), (∀ i, TB.WickVanishing.GP (b i)) → ev b f = 1 → IsUnit f := fun f b hb h => by
    have := congrArg MvPowerSeries.constantCoeff h
    rw [TB.WickVanishing.gt_const_ev_eq _ hb, map_one] at this
    rw [MvPowerSeries.isUnit_iff_constantCoeff, this]
    exact isUnit_one
  have g0 := TB.WickVanishing.gp_pt (k := V) (d := d) (0 : Fin 2)
  have g1 := TB.WickVanishing.gp_pt (k := V) (d := d) (1 : Fin 2)
  refine ⟨⟨(un _ _ (TB.WickVanishing.triple_points_zero_constant TB.WickVanishing.gp_zero₂ g0 g1) B.cocycleLeft_zero_fst).unit, rfl, fun n y z => ?_⟩,
    ⟨(un _ _ (TB.WickVanishing.triple_points_zero_constant g0 TB.WickVanishing.gp_zero₂ g1) B.cocycleRight_zero_snd).unit, rfl, fun n y z => ?_⟩⟩
  · have h : u3 (un _ _ (TB.WickVanishing.triple_points_zero_constant TB.WickVanishing.gp_zero₂ g0 g1) B.cocycleLeft_zero_fst).unit (1 : Sm B 2) (Sm.gen B 0) (Sm.gen B 1) = 1 :=
      Units.ext ((unitSeriesValueThreePoints_smallPoints (B := B) _ 0 (gen 0) (gen 1)).trans ((formalSeriesValueAtThreePoints_eq_ev _ _ _ _).trans B.cocycleLeft_zero_fst))
    have := congrArg (evU ![y, z]) h
    rwa [← unitSeriesValueThreePoints_substitution, map_one, map_one, Sm.sub_gen, Sm.sub_gen] at this
  · have h : u3 (un _ _ (TB.WickVanishing.triple_points_zero_constant g0 TB.WickVanishing.gp_zero₂ g1) B.cocycleRight_zero_snd).unit (Sm.gen B 0) (1 : Sm B 2) (Sm.gen B 1) = 1 :=
      Units.ext ((unitSeriesValueThreePoints_smallPoints (B := B) _ (gen 0) 0 (gen 1)).trans ((formalSeriesValueAtThreePoints_eq_ev _ _ _ _).trans B.cocycleRight_zero_snd))
    have := congrArg (evU ![y, z]) h
    rwa [← unitSeriesValueThreePoints_substitution, map_one, map_one, Sm.sub_gen, Sm.sub_gen] at this

omit hX hc hj hε in
theorem homAt_id_comp (p : limO V d n ⟶ t.G) : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (AlgHom.id V (PS V n d)) ≫ p = p := by
  rw [GermD.homAt_id, Category.id_comp]

omit hX hc hj hε in
theorem unit_ext_pref (j : t.PP.L.ι) {f g : (PS V n d)ˣ}
    (h : ∀ i : (z : Sp (PS V n d)) × {J // Pref t.PP.L j z J}, gu i.1 f = gu i.1 g) : f = g :=
  Units.ext (cstH_ext fun z => by
    obtain ⟨J, hJ⟩ := exists_pref t.PP.L j t.PP.isLB z
    exact congrArg Units.val (h ⟨z, J, hJ⟩))

omit hX hc hj hε in

theorem model_unit {tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)}
    (hc : IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg (fun j : Fin d => Pi.single j (1 : V)) x)
    (hf : IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e) {wP : PrimTyG t} (hP : IsPrimG t wP)
    (htr : FrTrunc t (𝟙 (Sp V)) d x e) (hs : Function.Surjective (t.G ⊗ t.G).hom.appTop.hom)
    {K : Type} [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] {h : PS K 2 d} (hh : B.IsCanonGauge K h)
    {Θ : PS V 3 d} {jo : PS V 1 d} (hΘ : IsTheta B K h H.w0 Θ) (hjo : IsIota B K h H.w0 jo) {k : ℕ} (hk : Odd k)
    {α : Fin d → V} (hα : Small α) (hαk : ∀ n, (Sm.const B α hα : Sm B n) ^ k = 1) (aV : baseOver (Sp V) ⟶ t.G)
    (haV : ∀ m : ℕ, ∃ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] V ⧸ maximalIdeal V ^ (m + 1),
      (∀ p, ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (α p.2)) ∧
      spMap (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))) ≫ aV.left =
        spMap (ψ : Jet V (Fin 1 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (x m).left) :
    ∃ (U : ThetaGrp t.G t.PP.L (k : ℤ) (baseOver (Sp V))) (u : PS V 1 d), SymLift t.G t.PP.L (k : ℤ) k aV U ∧
      TrUnit B Θ jo k α u ∧ ∀ (f : PS V 1 d) (σ σ' : LB.Sec (LPow t.G t.PP.L (k : ℤ) (baseOver (Sp V)))),
        IsGermG t (𝟙 (Sp V)) d x B.A.act e wP k σ f → IsActOf t.G t.PP.L (k : ℤ) U σ σ' →
        IsGermG t (𝟙 (Sp V)) d x B.A.act e wP k σ' (u * shift B.G.F (fun _ => α) f) := by
  obtain ⟨X, hX⟩ := GlobalTheory.T.exists_powerSeries_limit_of_compatible_jetPoints V t.G d x hc.trunc
  let a : ∀ n, Sm B n := fun n => Sm.const B α hα
  have ha : ∀ n, toBase _ ≫ aV = ptOf X (a n) := fun n => Over.OverMorphism.ext
    ((congrArg (· ≫ aV.left) (Category.comp_id _)).trans (GlobalTheory.T.constantSection_eq_limitChart_point V d _ B t.G x X hX α hα aV.left haV n).symm)
  have hak : aV ^ k = 1 := by
    have q : toBase (limO V d 0) ≫ aV ^ k = 1 := by
      rw [MonObj.comp_pow, ha]
      exact (map_pow (ptH hX hc 0) _ _).symm.trans ((congrArg _ (hαk 0)).trans (map_one _))
    let s : baseOver (Sp V) ⟶ limO V d 0 := Over.homMk (spMap (MvPowerSeries.constantCoeff : PS V 0 d →+* V)) (by
      show spMap _ ≫ spMap _ ≫ 𝟙 _ = 𝟙 _
      rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
      congr 2)
    have := congrArg (s ≫ ·) q
    simp only [← Category.assoc, MonObj.comp_one] at this
    rwa [base_ext (s ≫ _) (𝟙 _), Category.id_comp] at this
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_symmetric_lift_odd_order_localRing E H V t hs k hk aV hak
  obtain ⟨j, hj0⟩ := Geo.Tor.exists_chart t.PP.isLB (η[t.G].left (closedPoint V))
  have hj : ⊤ ≤ η[t.G].left ⁻¹ᵁ t.PP.L.U j :=
    ((IsLocalRing.closedPoint_mem_iff (R := V) (η[t.G].left ⁻¹ᵁ t.PP.L.U j)).1 hj0).ge
  obtain ⟨ε₀, hε⟩ := LinkEps.linkEps E H V t d _ _ _ _ _ _ tg x e wP hc hf hP htr j hj
  obtain ⟨ε, hε'⟩ := isUnit_eps hc hj hε
  obtain ⟨ρ, hρ⟩ := read_prim hX hc hj wP
  obtain ⟨θ, hθ⟩ := read_cub hX hc hj
  obtain ⟨φ, hφ⟩ := read_lift hX hc hj U (a 1) (hU.pt_eq ▸ ha 1)
  obtain ⟨⟨p₁, h₁, x₁⟩, p₂, h₂, x₂⟩ := exists_unit_ph (B := B)
  have cd := fun n (a b c : Sm B n) => cub_diff hX hc hj hε hf hε' h₁ h₂ hθ a b c
  have hθ' : ∀ n (i : (z : Sp (PS V n d)) × {J // Pref t.PP.L j z J}) (a b c : Sm B n),
      cubV t.cub (T := limO V d n) i.1 i.2.1 (ptH hX hc n a) (ptH hX hc n b) (ptH hX hc n c) = gu i.1 (u3 θ a b c) :=
    fun n i a b c => by
      have := hθ n _ (AlgHom.id V _) i.1 i.2.1 i.2.2 a b c
      simp only [homAt_id_comp] at this
      exact this
  have LL : ∀ n, LiftLaws (u3 θ) (u1 ρ) (u1 φ) (Sm.act B H.w0) (a n) k := fun n =>
    LiftLaws.pull (ptH hX hc n) (fun i : (z : Sp (PS V n d)) × {J // Pref t.PP.L j z J} => gu i.1)
      (fun u v => unit_ext_pref j) (w' := fun p => p ≫ t.act.act H.w0)
      (ρ' := fun i p => val wP p.left i.1 i.2.1)
      (φ' := fun i p => CommPairing.tval U (lift (toBase _) p).left i.1 i.2.1)
      (fun p => (ptOf_act hX hc _ p).symm) (hθ' n)
      (fun i p => by
        have := hρ n _ (AlgHom.id V _) i.1 i.2.1 i.2.2 p
        rw [homAt_id_comp] at this
        exact this)
      (fun i p => by
        have := hφ n _ (AlgHom.id V _) i.1 i.2.1 i.2.2 p (toBase _)
        rw [homAt_id_comp] at this
        exact this)
      (fun i => by
        have := GlobalTheory.T.symmetricLift_order_symmetry_multiplicativity E H _ t hs wP hP.1 k aV U hU (limO V d n) (toBase _) i.1 i.2.1 i.2.2.1
        rw [ha] at this
        exact this)
  have e₁ : ∀ n (z : Sm B n), u2 ε 1 z = 1 := fun n z => by
    have q : u3 θ 1 1 z = 1 := unit_ext_pref j fun i => by
      rw [← hθ', map_one, map_one]; exact (isCub_cubV t.cub i.2.2.1).face _ _
    have := (cd n 1 1 z).1
    rw [q, x₁, _root_.one_mul, _root_.one_mul, div_mul_cancel_left] at this
    exact inv_eq_one.1 this.symm
  have e₂ : ∀ n (z : Sm B n), u2 ε z 1 = 1 := fun n z => by
    have q : u3 θ z 1 1 = 1 := unit_ext_pref j fun i => by
      rw [← hθ', map_one, map_one]; exact (isCub_cubV t.cub i.2.2.1).face₂ _ _
    have := (cd n z 1 1).2
    rw [q, x₂, _root_.one_mul, _root_.one_mul, div_mul_cancel_left] at this
    exact inv_eq_one.1 this.symm
  let u : ∀ n, Sm B n → (PS V n d)ˣ := fun n => trU (u1 ρ) (u1 φ) (u2 ε) (Sm.act B H.w0) (a n) k
  have TL := fun n => trU_laws (Sm.act B H.w0) (LL n) (hαk n) (fun x y z => (cd n x y z).1) (fun x y z => (cd n x y z).2)
    (e₁ n) (e₂ n)
  have sa : ∀ {m n} (b : Fin m → Sm B n), Sm.sub b (a m) = a n := fun b => Sm.sub_const b α hα
  have us : ∀ {m n} (b : Fin m → Sm B n) (p : Sm B m), evU b (u m p) = u n (Sm.sub b p) := fun b p => by
    simp only [u, trU, map_mul (evU _), map_div (evU _), map_pow (evU _), ← besselUnipotentSubgroup_zero_subsingleton, ← unitSeriesValueTwoPoints_substitution, Sm.sub_act,
      map_mul (Sm.sub _), sa]
  have ev1 : ∀ {n} (p : Sm B n), evA ![p] (u 1 (Sm.gen B 0)).val = (u n p).val := fun p =>
    congrArg Units.val ((us ![p] _).trans (congrArg _ (Sm.sub_gen _ 0)))
  have sh : ∀ f, shift B.G.F (fun _ => α) f = evA ![a 1 * Sm.gen B 0] f := fun f => by
    rw [mul_comm, smallPointsSubstitutionAlgHom_single_point]
    exact congrArg (evV · f) (funext fun i => by fin_cases i; rfl)
  refine ⟨U, (u 1 (Sm.gen B 0)).val, hU, ⟨Units.isUnit _, ?_, ?_, ?_⟩, fun f σ σ' hg hact => ?_⟩
  · have q := congrArg Units.val ((TL 2).1 (Sm.gen B 0) (Sm.gen B 1))
    have r := GlobalTheory.T.eval_thetaSeries_mul_quadratic_partials V d _ B K h H.w0 hh p₁ p₂ h₁ h₂ Θ hΘ 2 (Sm.gen B 0) (Sm.gen B 1) (a 2)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, ← Units.eq_inv_of_mul_eq_one_right r] at q
    rw [← evA_one (B := B), ev1]
    exact (congrArg (· * _) ((smallPointsSubstitutionAlgHom_single_point (Sm.gen B 0 * Sm.gen B 1) _).symm.trans (ev1 _))).trans (q.trans
      (congrArg₂ (· * ·) (congrArg₂ (· * ·) ((ev1 _).symm.trans (smallPointsSubstitutionAlgHom_single_point _ _)) ((ev1 _).symm.trans (smallPointsSubstitutionAlgHom_single_point _ _)))
        (congrArg (· ^ k) (smallPointsSubstitutionAlgHom_three_points _ _ _ _))))
  · have it : ∀ i : ℕ, (fun f : PS V 1 d => (u 1 (Sm.gen B 0)).val * shift B.G.F (fun _ => α) f)^[i] 1 =
        (∏ l ∈ Finset.range i, u 1 (a 1 ^ l * Sm.gen B 0)).val := fun i => by
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [Function.iterate_succ_apply', ih, sh, ← evU_val, map_prod, Finset.prod_range_succ', pow_zero,
          _root_.one_mul, mul_comm, Units.val_mul]
        simp only [us, map_mul, map_pow, sa, Sm.sub_gen, Matrix.cons_val_zero, pow_succ, _root_.mul_assoc]
    rw [it, (TL 1).2.1, Units.val_one]
  · have q := congrArg Units.val (TL 0).2.2
    have r := GlobalTheory.T.eval_iotaSeries_eq_quadratic_inversion_partials V d _ B K h H.w0 hh p₁ p₂ h₁ h₂ jo hjo 0 (a 0)
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, ← r] at q
    rw [← evA_one (B := B), ev1]
    exact (congrArg₂ (· * ·) (congrArg (_ * · ^ k) (smallPointsSubstitutionAlgHom_single_point (a 0) _).symm)
      ((smallPointsSubstitutionAlgHom_single_point (a 0)⁻¹ _).symm.trans (ev1 _))).trans q
  · obtain ⟨f', hf'⟩ := germSt_holds E H _ t V (𝟙 _) d _ _ _ tg _ x _ _ _ _ e wP hc hf hP htr k σ'
    obtain ⟨S, hS⟩ := read_sec hX hc hj σ
    obtain ⟨S', hS'⟩ := read_sec hX hc hj σ'
    have g := germ_read hX hc hj hε hε' hρ hS hg
    have g' := germ_read hX hc hj hε hε' hρ hS' hf'
    have id1 : ∀ f : PS V 1 d, evA ![(Sm.gen B 0 : Sm B 1)] f = f := fun f =>
      (congrArg (evA · f) (funext fun j => by fin_cases j; rfl)).trans (evA_gen f)
    have key : S' = (u1 φ (Sm.gen B 0)).val * evA ![a 1 * Sm.gen B 0] S := cstH_ext fun z => by
      obtain ⟨J, hJ⟩ := exists_pref t.PP.L j t.PP.isLB z
      have q := twist_val hact (lift (toBase _) (ptOf X (Sm.gen B (0 : Fin 1)))).left z hJ.1
      have b₁ := hS' 1 _ (AlgHom.id V _) z J hJ (Sm.gen B 0) (toBase _)
      have b₂ := hS 1 _ (AlgHom.id V _) z J hJ (a 1 * Sm.gen B 0) (toBase _)
      have b₃ := hφ 1 _ (AlgHom.id V _) z J hJ (Sm.gen B 0) (toBase _)
      rw [homAt_id_comp] at b₁ b₂ b₃
      rw [← Over.comp_left, lift_transl, show toBase _ ≫ U.pt = ptOf X (a 1) from hU.pt_eq ▸ ha 1, ← ptOf_mul hX hc] at q
      rw [id1] at b₁
      rw [map_mul]
      exact b₁.symm.trans (q.trans (congrArg₂ (· * ·) (congrArg Units.val b₃) b₂))
    have : f' = (u 1 (Sm.gen B 0)).val * shift B.G.F (fun _ => α) f := by
      rw [g, g', map_mul, ← evU_val, map_pow, map_mul, ← besselUnipotentSubgroup_zero_subsingleton, ← unitSeriesValueTwoPoints_substitution, Sm.sub_act, Sm.sub_gen] at key
      rw [sh, (Units.eq_mul_inv_iff_mul_eq _).2 key]
      simp only [u, trU, Matrix.cons_val_zero, div_eq_mul_inv, mul_pow, inv_pow, mul_inv, Units.val_mul]
      ring
    exact this ▸ hf'

end Model

theorem exists_trUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (Θ : PS T.V 3 (chD C.ch)) (jo : PS T.V 1 (chD C.ch)), IsTheta B T.Fr (gaugeOf C) H.w0 Θ → IsIota B T.Fr (gaugeOf C) H.w0 jo → ∀ (k : ℕ), Odd k → ∀ (a : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) α, FormPt C a α → a ^ k = 1 → ∃ u : PS T.V 1 (chD C.ch), TrUnit B Θ jo k α u ∧ ∀ (F F' : SecN Xo (xOf y) k) (f : PS T.V 1 (chD C.ch)), Regular C k F → GermIs C k F f → Moves Xo a F F' → GermIs C k F' (u * shift B.G.F (fun _ => α) f) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hC B hB Θ jo hΘ hjo k hk a α hFP hak
  obtain ⟨f1, fu, fm, -, -⟩ := GlobalTheory.PlaceFormPt.formPt_spec E H Dw l Xo c hstar T io y C B hB
  have hh := ((integralBiext_gauge_eig_bound E H Dw l Xo c hstar T io y C).choose_spec.2 B hB).1
  have hα := hFP.1
  have hαk : ∀ n, (Sm.const B α hα : Sm B n) ^ k = 1 := by
    have cc : ∀ p : Sm B 0, (cpt fun i => MvPowerSeries.constantCoeff (p.1 i) : Pt T.V 0 (chD C.ch)) = p.1 :=
      fun p => funext fun i => MvPowerSeries.ext fun e => by
        obtain rfl : e = 0 := Subsingleton.elim _ _
        simp [cpt]
    have pw : ∀ i : ℕ, FormPt C (a ^ i) fun l => MvPowerSeries.constantCoeff (((Sm.const B α hα : Sm B 0) ^ i).1 l) := by
      intro i
      induction i with
      | zero => rw [pow_zero, pow_zero]; exact (congrArg (FormPt C 1) (funext fun l => map_zero MvPowerSeries.constantCoeff)).mpr f1
      | succ i ih => rw [pow_succ]; exact fm _ _ _ _ _ ih hFP (by rw [cc, cc, pow_succ]; rfl)
    have z := (fu _ _ _ _ (pw k) f1).1 hak
    have z0 : (Sm.const B α hα : Sm B 0) ^ k = 1 := Subtype.ext (by
      rw [← cc, z]; exact funext fun i => map_zero _)
    intro n
    rw [← Sm.sub_const (Fin.elim0 : Fin 0 → Sm B n), ← map_pow, z0, map_one]
  obtain ⟨-, aV, r, h0, r0, r1, r2, hψ⟩ := hFP
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hB
  obtain ⟨U, u, hU, hu, hg⟩ := model_unit (B := B) (t := C.I.G) (x := C.xT) (e := C.eT) (b1 ▸ b2 ▸ C.chartT)
    (b1 ▸ b2 ▸ b3 ▸ b4 ▸ b5 ▸ b6 ▸ C.frameT) C.primT hC
    (ModelSquareFunctions.surjective_appTop_square E H Dw l Xo c T io y.1 C.I) hh hΘ hjo hk hα hαk
    (Over.homMk aV h0) hψ
  refine ⟨u, hu, fun F F' f hF hf hm => GlobalTheory.T.germ_symmetricTranslate_fibre_eq_model E H Dw l Xo c hstar T io y C hC k hk a _ r r0 r1 r2 U hU F F' f _
    hF hf hm fun σ σ' => ?_⟩
  rw [← b2]
  exact hg f σ σ'

end GlobalTheory.TransUnit
