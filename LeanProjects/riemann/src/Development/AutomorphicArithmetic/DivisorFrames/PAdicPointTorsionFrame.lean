import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AutomorphicArithmetic.DivisorFrames.AlgebraicPAdicPointLifts
import Development.AutomorphicArithmetic.DivisorFrames.LevelReductionTorsionCharacter
import Development.AutomorphicArithmetic.DivisorFrames.WeilPairingLabelsTorsionPoints
import Development.AutomorphicArithmetic.DivisorFrames.TateModulePairingCongruence
import Development.AutomorphicArithmetic.DivisorFrames.TangentBasisLieCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLatticeSpansStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.RootFrame
open scoped NNReal
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

private theorem comp_pow' {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

private theorem pow_eq_one_of' {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    {φ : A'.left ⟶ A.left} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left} {x : T ⟶ A} {x' : T' ⟶ A'}
    (gp : IsGrpPullback A' A f φ) (hx : x'.left ≫ φ = h ≫ x.left) {n : ℕ} (hn : x ^ n = 1) : x' ^ n = 1 := by
  have hb : h ≫ T.hom = T'.hom ≫ f := by
    rw [← Over.w x, ← Category.assoc, ← hx, Category.assoc, gp.1.w, ← Category.assoc, Over.w x']
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv gp T' (T'.hom ≫ f) rfl
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk h hb
  have e₁ : e x' = ρ ≫ x := Over.OverMorphism.ext ((he x').trans hx)
  apply e.injective
  rw [map_pow, map_one, e₁, ← comp_pow', hn, MonObj.comp_one]

private theorem label_move {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] {n : ℕ}
    {yb : Sp 𝓞_ℂ_[p] ⟶ Z.X} {yy : Sp ℂ_[p] ⟶ Xo.XF c} {P : PtP E p} {π : P.G.left ⟶ Z.t.G.left}
    {ψ : P.A.A.left ⟶ Z.oF.t.G.left} (hP : PtOnG Z yb yy P π ψ) {ch : Dw.La → TorsChar Z.t yb (p ^ n)}
    (hch : WeilLab Z (algebraMap 𝓞_ℂ_[p] ℂ_[p]) yb yy (p ^ n) ch) :
    ∃ (lb : Dw.La → GlobalTheory.ChTor.Pts P.A.A) (ζ : ℂ_[p]ˣ), IsPrimitiveRoot ζ (p ^ n) ∧ (∀ a b, lb (a + b) = lb a * lb b) ∧
      (∀ (o : 𝓞 E) a, lb (o • a) = lb a ≫ P.oA.act o) ∧ (∀ σ : GlobalTheory.ChTor.Pts P.A.A, σ ^ (p ^ n) = 1 ↔ ∃ a, lb a = σ) ∧
      (∀ a b, weil P.A (p ^ n) (lb a) (lb b) = ζ ^ Dw.EF a b) ∧
      ∀ a (w : Over.mk (spMap (algebraMap 𝓞_ℂ_[p] 𝓞_ℂ_[p]) ≫ yb) ⟶ Z.t.G) (z : GlobalTheory.ChTor.Pts P.A.A), w ^ (p ^ n) = 1 →
        z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w.left →
        algebraMap 𝓞_ℂ_[p] ℂ_[p] ((ch a).χ 𝓞_ℂ_[p] w : 𝓞_ℂ_[p]ˣ) = (weil P.A (p ^ n) (lb a) z : ℂ_[p]) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  obtain ⟨lb, ζ, ⟨hζ, hadd, hlinb, honto, hisom⟩, hχ⟩ := hch
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h4 (Over.mk (𝟙 _)) yy (Category.id_comp _).symm
  have hact : ∀ o : 𝓞 E, (P.oA.act o).left ≫ ψ = ψ ≫ (Z.oF.t.act.act o).left := by
    intro o
    apply Z.m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, h5, Z.m.act o, ← Category.assoc ψ, h5, ← Category.assoc, P.gen_act o,
        Category.assoc, Category.assoc, h3 o]
    · rw [Category.assoc, Category.assoc, Over.w (Z.oF.t.act.act o), h4.1.w, ← Category.assoc, Over.w]
  have hlin : ∀ (x : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A) (o : 𝓞 E), e (x ≫ P.oA.act o) = e x ≫ Z.oF.t.act.act o := by
    intro x o
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, hact]
  have hsymm : ∀ y : Over.mk yy ⟶ Z.oF.t.G, (e.symm y).left ≫ ψ = y.left := fun y => by
    rw [← he, MulEquiv.apply_symm_apply]
  have hweil : ∀ (g : Sp ℂ_[p] ⟶ Xo.XF c), 𝟙 _ ≫ yy = g → ∀ (k : ℤ) (x y : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)
      (x₀ y₀ : Over.mk g ⟶ Z.oF.t.G) (c : (Γ(Sp ℂ_[p], ⊤))ˣ), x₀.left = x.left ≫ ψ → y₀.left = y.left ≫ ψ →
      (Out.WeilIs P.A.A P.A.L k x y c ↔ Out.WeilIs Z.oF.t.G Z.oF.t.PP.L k x₀ y₀ c) := by
    rintro g rfl k x y x₀ y₀ c hx hy
    exact GlobalTheory.weilIs_grpPullback_of_comm _ _ Z.oF.t.G P.A.A yy ψ Z.oF.t.PP.L P.A.L Z.oF.t.PP.isLB P.A.isLB h4 h6
      (Over.mk (𝟙 _)) k x y x₀ y₀ c hx hy
  have onto : ∀ x : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A, x ^ (p ^ n) = 1 ↔ ∃ a, e.symm (lb a) = x := by
    intro x
    rw [← e.injective.eq_iff, map_pow, map_one, honto]
    simp only [MulEquiv.symm_apply_eq]
  have hw : ∀ a b, weil P.A (p ^ n) (e.symm (lb a)) (e.symm (lb b)) = ζ ^ Dw.EF a b := by
    intro a b
    have hza : (e.symm (lb a)) ^ (p ^ n) = 1 := (onto _).2 ⟨a, rfl⟩
    have hzb : (e.symm (lb b)) ^ (p ^ n) = 1 := (onto _).2 ⟨b, rfl⟩
    refine ((GlobalTheory.HTLat.weilIs_iff (A := P.A) (Nat.one_le_iff_ne_zero.2 (pow_pos hp n).ne') hza hzb _).1 ?_).symm
    rw [hweil yy (Category.id_comp yy) _ _ _ (lb a) (lb b) _ (hsymm _).symm (hsymm _).symm]
    exact hisom a b
  refine ⟨fun a => e.symm (lb a), ζ, hζ, fun a b => by simp only [hadd, map_mul], fun o a => ?_, onto, hw,
    fun a w z hwp hz => ?_⟩
  · apply e.injective
    rw [hlin, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hlinb o a
  · have hzp : z ^ (p ^ n) = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      refine pow_eq_one_of' Z.m.cart (h := spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ?_ hwp
      rw [he, Category.assoc, h5, hz]
    obtain ⟨b, rfl⟩ := (onto z).1 hzp
    rw [hw]
    apply hχ a b w hwp
    rw [← hsymm (lb b), Category.assoc, h5, hz]

private theorem isot_bLie {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p)
    (hK : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P) {g : ℕ} (x : Fin g → LieG P.Gt) (v v' : Fin g → ℂ_[p]) :
    P.pairV (∑ k, v k • P.bLie (x k)) (∑ k, v' k • P.bLie (x k)) = 0 := by
  obtain ⟨-, -, -, -, hann, -, hspanW⟩ := hK
  have hLW : ∀ cf : Fin g → ℂ_[p], ∑ k, cf k • P.bLie (x k) ∈ P.W := fun cf => by
    rw [hspanW]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  exact (hann _).1 (hLW v) _ (hLW v')

private theorem norm_le_of_mem {p : ℕ} [Fact p.Prime] {n : ℕ} {y : 𝓞_ℂ_[p]}
    (hmem : y ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) : ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] y‖ ≤ (p : ℝ)⁻¹ ^ n := by
  obtain ⟨d, hd'⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [← hd', map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  have e2 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  rw [e2]
  have e3 : ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] d‖ ≤ 1 := (GlobalTheory.PadicComplexHost.mem_iff_norm _ _).1 d.2
  exact mul_le_of_le_one_left (by positivity) e3

theorem UpperTheory.p_adic_point_torsion_frame :
    GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) [IsLocallyNoetherian Z.X], Z.X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X) (yy : Sp ℂ_[p] ⟶ Xo.XF c), 1 ≤ n → spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = yy ≫ Z.j → AlgDef (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) → ∀ ch : Dw.La → TorsChar Z.t yb (p ^ n), WeilLab Z (algebraMap 𝓞_ℂ_[p] ℂ_[p]) yb yy (p ^ n) ch → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Z.t.G.left)), IsTanBasis Z.t yb e → ∃ b, HTLin Dw Z.t p n (algebraMap 𝓞_ℂ_[p] ℂ_[p]) yb ch e b := by
  intro hHT E _ _ _ H Dw l Xo c Z _ hsep p _ n yb yy hn hy halg ch hch g ee hee
  letI := H.starRing
  obtain ⟨P, π, ψ, hP⟩ := UpperTheory.algebraic_p_adic_point_lifts E H Dw l Xo c Z p yb yy hy halg
  obtain ⟨hLR, -, -, hK⟩ := hHT p ℂ_[p] _ 𝓞_ℂ_[p] (𝓞 E) P
  obtain ⟨lb, ζ, hζ, hadd, hlin, onto, hw, hχ⟩ := label_move Z hP hch
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  obtain ⟨f, u, hflev, hflin, hu, hpair⟩ := UpperTheory.weil_pairing_labels_torsion_points E H Dw p n P lb ζ hn hζ hadd hlin onto hw
  have hspan := GlobalTheory.T.tate_lattice_spans E H Dw p P f (fun x hx => by
    obtain ⟨t, ht⟩ := (tate_free_of_card p _ _ P.card_torsion).2.1 1 x (by rw [pow_one]; exact hx)
    obtain ⟨a, ha⟩ := (onto _).1 (GlobalTheory.HTLat.Tate.lev_pow t n)
    refine ⟨a, ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [← ht, ← GlobalTheory.HTLat.Tate.lev_add_pow (f a) 1 k, ← GlobalTheory.HTLat.Tate.lev_add_pow t 1 k, hflev, ha])
  obtain ⟨B, hB1, hB2, hB3⟩ := UpperTheory.tate_module_pairing_congruence E H Dw p n (fun _ => rfl) P f u hn hspan hflin hu hpair
  obtain ⟨x, hx1, hx2⟩ := UpperTheory.tangent_basis_lie_coordinates E H Z.X Z.t p P yb π h2 h3 g ee hee
  obtain ⟨L, hL⟩ : ∃ L : (Fin g → ℂ_[p]) →ₗ[ℂ_[p]] P.V, ∀ cf, L cf = ∑ k, cf k • P.bLie (x k) :=
    ⟨Fintype.linearCombination ℂ_[p] fun k => P.bLie (x k), fun cf => Fintype.linearCombination_apply _ _ _⟩
  refine ⟨B ∘ₗ L, fun a h hd i => ?_, fun cf w hcw σ hσ => ?_, fun v v' hv hv' => ?_⟩
  · have hmem := UpperTheory.level_reduction_torsion_character E H Z.X Z.t hsep p n P yb π h2 hLR (f a) (ch a) (fun w z hwp hz => by
      rw [hflev]
      exact hχ a w z hwp hz) g ee h hee.1 hd i (x i) (hx1 i)
    have e1 : L (Pi.single i 1) = P.bLie (x i) := by
      simp [hL, Pi.single_apply]
    rw [LinearMap.comp_apply, hB1, e1, Point.pairV_bLie, sub_neg_eq_add, ← map_add]
    exact norm_le_of_mem hmem
  · refine hB2 _ σ ?_
    rw [hL]
    exact hx2 cf w hcw σ hσ
  · refine hB3 (L v) (L v') ?_ hv hv'
    rw [hL, hL]
    exact isot_bLie P hK x v v'
