import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMorphismOfCompatibleFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtIntegralPoint
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieFilt

open GlobalTheory.TangentOrigin (evalPt evalPt_res)

theorem evalPt_appLE_of_eq {K : Type} [CommRing K] {X Y : Scheme.{0}} (y : Sp K ⟶ Y) (π : Y ⟶ X) {x : Sp K ⟶ X}
    (hx : y ≫ π = x) (U : X.Opens) (V : Y.Opens) (e : V ≤ π ⁻¹ᵁ U) (hV : ⊤ ≤ y ⁻¹ᵁ V) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : evalPt y V hV (π.appLE U V e f) = evalPt x U hU f := by
  subst hx
  have := Scheme.Hom.appLE_comp_appLE y π U V ⊤ e hV
  unfold evalPt
  rw [← this]
  rfl

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem tanEv_change {Y : Scheme.{0}} (t : SAB H Y) {K : Type} [CommRing K] {x : Sp K ⟶ Y}
    {v : Sp (DualNumber K) ⟶ t.G.left} (hv : IsTanAtG t x v) {g : ℕ} (ch ch' : VB.Chart (omega t.G) g)
    (h : ⊤ ≤ x ⁻¹ᵁ ch.U) (h' : ⊤ ≤ x ⁻¹ᵁ ch'.U) (h'' : ⊤ ≤ x ⁻¹ᵁ (ch'.U ⊓ ch.U)) (k : Fin g) :
    tanEv t hv h (ch.e k) = ∑ b, evalPt x _ h'' (trCo ch'.isFrame ch.e b k) * tanEv t hv h' (ch'.e b) := by
  let L : Γ(omega t.G, ch'.U ⊓ ch.U) →+ K := AddMonoidHom.mk' (tanEv t hv h'') (GlobalTheory.LocM.tanEv_add t hv h'')
  have e := congrArg L
    ((ch'.isFrame.basis (inf_le_left : ch'.U ⊓ ch.U ≤ ch'.U)).sum_repr (Twist.resM _ inf_le_right (ch.e k)))
  rw [map_sum] at e
  refine ((GlobalTheory.LocM.tanEv_resM t hv h'' inf_le_right _).symm.trans e.symm).trans (Finset.sum_congr rfl fun b _ => ?_)
  refine (GlobalTheory.LocM.tanEv_smul t hv h'' _ _).trans ?_
  rw [VB.IsFrame.basis_apply, GlobalTheory.LocM.tanEv_resM]
  rfl

variable {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
  {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} (ρ : X ⟶ Z.X) {d : ℕ}

theorem genCoord_compat (hq : IsArithVar q d)
    (hW : IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)))
    (hρ : jB ≫ ρ = πB ≫ genι Z) {L : X.Modules} {g : ℕ}
    {ℓ : ∀ ch : VB.Chart (omega Z.t.G) g, Fin g → Γ(L, ρ ⁻¹ᵁ ch.U)} (hℓ : ∀ ch, VB.IsFrame (ℓ ch))
    (hD : DualCharts ρ ℓ hℓ) {M : X.Modules} {r : ℕ} {τ : E →+* ℂ} {t : FrAssign Z M r jB}
    (ht : IsLieFrames Z e jB πB M r τ false t) {ch ch' : VB.Chart (omega Z.t.G) g} {V V' : X.Opens}
    (hV : V ≤ ρ ⁻¹ᵁ ch.U) (hV' : V' ≤ ρ ⁻¹ᵁ ch'.U) {f : Fin r → Γ(M, V)} (hf : VB.IsFrame f)
    {f' : Fin r → Γ(M, V')} (hf' : VB.IsFrame f') {A : Matrix (Fin g) (Fin r) Γ(X, V)}
    {A' : Matrix (Fin g) (Fin r) Γ(X, V')} (hA : GenCoord Z jB πB t ch hf (A.map (jB.app V)))
    (hA' : GenCoord Z jB πB t ch' hf' (A'.map (jB.app V'))) (a : Fin r) :
    Twist.resM L (inf_le_right : V ⊓ V' ≤ V') (∑ b, A' b a • Twist.resM L hV' (ℓ ch' b)) =
      ∑ b, trCo hf f' b a • Twist.resM L (inf_le_left : V ⊓ V' ≤ V) (∑ k, A k b • Twist.resM L hV (ℓ ch k)) := by
  have hI : V ⊓ V' ≤ ρ ⁻¹ᵁ ch.U ⊓ ρ ⁻¹ᵁ ch'.U := inf_le_inf hV hV'
  have key : ∀ k, ∑ b, resG X (inf_le_right : V ⊓ V' ≤ V') (A' b a) * resG X hI (trCo (hℓ ch) (ℓ ch') k b) =
      ∑ b, trCo hf f' b a * resG X (inf_le_left : V ⊓ V' ≤ V) (A k b) := by
    intro k
    rcases ((V ⊓ V' : X.Opens) : Set X).eq_empty_or_nonempty with hE | hE
    · have hb : V ⊓ V' = ⊥ := TopologicalSpace.Opens.coe_eq_empty.1 hE
      haveI : Subsingleton Γ(X, V ⊓ V') :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hb)
      exact Subsingleton.elim _ _
    obtain ⟨K, _, x, ψ, hψ, h, hinj⟩ := exists_generic_evalPt_injective hq hW _ hE
    have hU : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ V := h.trans ((x ≫ jB).preimage_mono inf_le_left)
    have hU' : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ V' := h.trans ((x ≫ jB).preimage_mono inf_le_right)
    have hII : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (ρ ⁻¹ᵁ ch.U ⊓ ρ ⁻¹ᵁ ch'.U) := h.trans ((x ≫ jB).preimage_mono hI)
    have hy : (x ≫ jB) ≫ ρ = x ≫ πB ≫ genι Z := by rw [Category.assoc, hρ]
    have hc : ⊤ ≤ (x ≫ πB ≫ genι Z) ⁻¹ᵁ ch.U := by
      rw [← hy]; exact hU.trans ((x ≫ jB).preimage_mono hV)
    have hc' : ⊤ ≤ (x ≫ πB ≫ genι Z) ⁻¹ᵁ ch'.U := by
      rw [← hy]; exact hU'.trans ((x ≫ jB).preimage_mono hV')
    have hcc : ⊤ ≤ (x ≫ πB ≫ genι Z) ⁻¹ᵁ (ch'.U ⊓ ch.U) := fun p hp => ⟨hc' hp, hc hp⟩
    have bf := ht.1 V f hf K x hU ψ hψ
    obtain ⟨hv, hcomb⟩ := GlobalTheory.TanSec.Norm.exists_tanEv_comb Z.t hc ch.isFrame (fun i => (bf.1 i).1)
      (ht.2.1 V V' f f' hf hf' K x hU hU' h a)
    have e1 (b : Fin r) : evalPt (x ≫ jB) V hU (A k b) = tanEv Z.t (bf.1 b).1 hc (ch.e k) := by
      rw [← hA K x hU hU b _ hc k, Matrix.map_apply, Matrix.map_apply, Scheme.Hom.app_eq_appLE]
      exact (evalPt_appLE_of_eq x jB rfl _ _ _ _ _ _).symm
    have e2 (b : Fin g) : evalPt (x ≫ jB) V' hU' (A' b a) = tanEv Z.t hv hc' (ch'.e b) := by
      rw [← hA' K x hU' hU' a _ hc' b, Matrix.map_apply, Matrix.map_apply, Scheme.Hom.app_eq_appLE]
      exact (evalPt_appLE_of_eq x jB rfl _ _ _ _ _ _).symm
    have e3 (b : Fin g) : evalPt (x ≫ jB) _ hII (trCo (hℓ ch) (ℓ ch') k b) =
        evalPt (x ≫ πB ≫ genι Z) _ hcc (trCo ch'.isFrame ch.e b k) := by
      rw [hD]
      exact evalPt_appLE_of_eq _ ρ hy _ _ _ _ _ _
    apply hinj
    simp only [map_sum, map_mul]
    simp only [evalPt_res (x ≫ jB) inf_le_left hU h, evalPt_res (x ≫ jB) inf_le_right hU' h,
      evalPt_res (x ≫ jB) hI hII h, e1, e2, e3]
    rw [← hcomb k, tanEv_change Z.t hv ch ch' hc hc' hcc k]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  refine ((hℓ ch).basis ((inf_le_left : V ⊓ V' ≤ V).trans hV)).ext_elem fun k => ?_
  have e1 (b : Fin g) : Twist.resM L (inf_le_left : V ⊓ V' ≤ V) (Twist.resM L hV (ℓ ch b)) =
      (hℓ ch).basis (inf_le_left.trans hV) b := by
    rw [VB.IsFrame.basis_apply, Twist.resM_resM]
  have e2 (b : Fin g) : ((hℓ ch).basis ((inf_le_left : V ⊓ V' ≤ V).trans hV)).repr
      (Twist.resM L (inf_le_right : V ⊓ V' ≤ V') (Twist.resM L hV' (ℓ ch' b))) k =
      resG X hI (trCo (hℓ ch) (ℓ ch') k b) := by
    rw [trCo, ← (hℓ ch).repr_resM inf_le_left hI, Twist.resM_resM, Twist.resM_resM]
  simp only [map_sum, Twist.resM_smul, e1, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, e2]
  exact key k

end Free

theorem exists_tanCoord : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} (ρ : X ⟶ Z.X) {d : ℕ}, IsArithVar q d → IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) → jB ≫ ρ = πB ≫ genι Z →
    ∀ {L : X.Modules} {g : ℕ} {ℓ : ∀ ch : VB.Chart (omega Z.t.G) g, Fin g → Γ(L, ρ ⁻¹ᵁ ch.U)} (hℓ : ∀ ch, VB.IsFrame (ℓ ch)), IsVB (omega Z.t.G) g → DualCharts ρ ℓ hℓ →
    ∀ {M : X.Modules} {r : ℕ} (τ : E →+* ℂ) (t : FrAssign Z M r jB), IsVB M r → IsLieFrames Z e jB πB M r τ false t →
    (∀ (ch : VB.Chart (omega Z.t.G) g) (V : X.Opens), V ≤ ρ ⁻¹ᵁ ch.U → IsAffineOpen V →
      ∀ (f : Fin r → Γ(M, V)) (hf : VB.IsFrame f), ∃ A₀ : Matrix (Fin g) (Fin r) Γ(X, V),
        GenCoord Z jB πB t ch hf (A₀.map (jB.app V))) →
    ∃ T : M ⟶ L, TanCoord Z jB πB t ρ hℓ T := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB ρ d hq hW hρ L g ℓ hℓ hω hD M r τ t hM ht hA
  have ex (x : X) : ∃ (ch : VB.Chart (omega Z.t.G) g) (V : X.Opens) (_ : V ≤ ρ ⁻¹ᵁ ch.U) (f : Fin r → Γ(M, V))
      (hf : VB.IsFrame f) (A : Matrix (Fin g) (Fin r) Γ(X, V)), x ∈ V ∧
        GenCoord Z jB πB t ch hf (A.map (jB.app V)) := by
    obtain ⟨U, m, hU, hm⟩ := hω (ρ x)
    obtain ⟨U', f, hU', hf⟩ := hM x
    obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ρ ⁻¹ᵁ U ⊓ U') ⟨hU, hU'⟩
    have hle' : V ≤ ρ ⁻¹ᵁ U ⊓ U' := hle
    obtain ⟨A, hA'⟩ := hA ⟨U, m, hm⟩ V (hle'.trans inf_le_left) hV _ (hf.res (hle'.trans inf_le_right))
    exact ⟨⟨U, m, hm⟩, V, hle'.trans inf_le_left, _, _, A, hx, hA'⟩
  choose ch V hV f hf A hx hAc using ex
  obtain ⟨T, hT⟩ := GlobalTheory.FrameGlue.exists_hom_of_frames X M L r X V (fun x => ⟨x, hx x⟩) f hf
    (fun x i => ∑ b, A x b i • Twist.resM L (hV x) (ℓ (ch x) b))
    fun x y a => genCoord_compat Z e ρ hq hW hρ hℓ hD ht (hV x) (hV y) (hf x) (hf y) (hAc x) (hAc y) a
  refine ⟨T, fun ch₀ V₀ hV₀ haff f₀ hf₀ => ?_⟩
  obtain ⟨A₀, hA₀⟩ := hA ch₀ V₀ hV₀ haff f₀ hf₀
  have key (i : Fin r) : T.app V₀ (f₀ i) = ∑ b, A₀ b i • Twist.resM L hV₀ (ℓ ch₀ b) := by
    refine Twist.sec_ext_of_cover (fun x : X => V x ⊓ V₀) (fun _ => inf_le_right)
      (fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hx y, hy⟩) fun x => ?_
    rw [genCoord_compat Z e ρ hq hW hρ hℓ hD ht (hV x) hV₀ (hf x) hf₀ (hAc x) hA₀ i, ← Twist.app_resM,
      ← ((hf x).basis (inf_le_left : V x ⊓ V₀ ≤ V x)).sum_repr (Twist.resM M inf_le_right (f₀ i)), map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Scheme.Modules.Hom.app_smul, VB.IsFrame.basis_apply, Twist.app_resM, hT]
    rfl
  have e0 : (Matrix.of fun b i => jB.app V₀ (((hℓ ch₀).basis hV₀).repr (T.app V₀ (f₀ i)) b)) =
      A₀.map (jB.app V₀) := by
    ext b i : 2
    rw [Matrix.of_apply, Matrix.map_apply, key]
    simp only [← (hℓ ch₀).basis_apply hV₀, Module.Basis.repr_sum_self]
  rw [e0]
  exact hA₀

end GlobalTheory.LieFilt

end
