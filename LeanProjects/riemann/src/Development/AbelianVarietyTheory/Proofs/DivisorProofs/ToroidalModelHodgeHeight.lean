import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelBaseChangeNormal
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

namespace GlobalTheory.LieFilt.Reg

open GlobalTheory.ShFam.Pad.Guard

theorem norm_tanEv_le_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) (hX : X.IsSeparated) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    {xO : Sp ↥(intO C) ⟶ X} {x : Sp C ⟶ X} (hx : spMap (intO C).subtype ≫ xO = x) {V : X.Opens}
    (hO : ⊤ ≤ xO ⁻¹ᵁ V) (hV : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} {m : Fin n → Γ(omega t.G, V)} (hm : VB.IsFrame m)
    {v : Sp (DualNumber C) ⟶ t.G.left} (hv : IsTanAtG t x v) {δ : C} (hδ : ‖δ‖ = 1)
    (h : spMap (epsMul δ) ≫ v ∈ latDR t x) (b : Fin n) : ‖tanEv t hv hV (m b)‖ ≤ 1 := by
  have hu : ∀ k : Fin 1, IsTanAtG t x ((fun _ => v) k) := fun _ => hv
  obtain ⟨hw, he⟩ := GlobalTheory.TanSec.Norm.exists_tanEv_comb t hV hm hu (comb_smul hu (isCombAtG_single t x hu 0) δ)
  have h1 : ‖tanEv t hw hV (m b)‖ ≤ 1 := (GlobalTheory.TanSec.Norm.mem_latDR_iff_tanEv t hX hx hO hV hm hw).1 h b
  rw [he b] at h1
  simpa [hδ] using h1

theorem exists_regular : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} (ρ : X ⟶ Z.X) {d : ℕ}, IsArithVar q d → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) → jB ≫ ρ = πB ≫ genι Z →
    ∀ {M : X.Modules} {r g : ℕ} (τ : E →+* ℂ) (t : FrAssign Z M r jB), IsLieFrames Z e jB πB M r τ false t →
    IsLieLat Z e jB πB M r τ (ArIn.ind ∅) (fun _ => True) t →
    ∀ (ch : VB.Chart (omega Z.t.G) g) (V : X.Opens), V ≤ ρ ⁻¹ᵁ ch.U → IsAffineOpen V →
    ∀ (f : Fin r → Γ(M, V)) (hf : VB.IsFrame f) (A : Matrix (Fin g) (Fin r) Γ(W, jB ⁻¹ᵁ V)), GenCoord Z jB πB t ch hf A →
    ∃ A₀ : Matrix (Fin g) (Fin r) Γ(X, V), A₀.map (jB.app V) = A := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB ρ d hq hn pb hρ M r g τ t ht hL ch V hle hV f hf A hA
  have hI := IntCritPf.intCrit F X W q _ jB d hq hn pb
  have : IsProper Z.s := projProper _ _ _ Z.proj
  have hsep : Z.X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from Z.s]; infer_instance⟩
  have key : ∀ b i, ∃ f₀ : Γ(X, V), jB.app V f₀ = A b i := fun b i => by
    refine hI _ hV _ fun v ε xg xt h1 h2 h3 hx => ?_
    obtain ⟨hp, hio, -⟩ := ioOf_spec F v ε
    haveI : Fact (resP v).Prime := ⟨hp⟩
    have hxU : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ V := fun p hp => hx hp
    obtain ⟨δ, hδ, hd⟩ := CoordReg.lieLat_at Z hL v hp ε xg xt h1 h2 V f hf h3 hxU
    have hk : ArIn.ind ∅ (resP v) = false := by simp [ArIn.ind]
    rw [CoordReg.lat_ind_empty] at hd
    have hδ1 : ‖δ‖ = 1 := by
      rw [hδ, if_neg (fun h => Bool.false_ne_true (hk.symm.trans h.1)), neg_zero, Real.rpow_zero]
    generalize ioOf (resP v) ε = io at hio hd
    have h4 : (spMap io ≫ xg) ≫ πB ≫ genStr Z ≫ spMap e.toRingHom =
        spMap (io.comp (algebraMap F (AlgebraicClosure F))) := by
      rw [Category.assoc, h1, sp_comp]
    have hy : ⊤ ≤ ((spMap io ≫ xg) ≫ jB) ⁻¹ᵁ V := fun p _ => hxU (Set.mem_univ _)
    have b2 := ht.1 V f hf _ _ hy _ h4
    rw [show t V f hf _ _ hy = _ from funext fun k => ht.2.2 V f hf _ _ _ xg hxU hy k, Category.assoc] at b2
    have h5 := (hd _ (b2.1 i)).1 ⟨Pi.single i 1, fun k => by
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk], isCombAtG_single Z.t _ (fun j => (b2.1 j).1) i⟩
    let ioO : ε.O →+* intO ℂ_[resP v] := (io.comp ε.O.subtype).codRestrict _ fun b => (hio b).2 b.2
    have hx0 : spMap (intO ℂ_[resP v]).subtype ≫ spMap ioO ≫ xt ≫ ρ = spMap io ≫ xg ≫ πB ≫ genι Z := by
      rw [← hρ, ← Category.assoc xg, ← h2, ← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc,
        sp_comp, sp_comp]
      rfl
    have hO : ⊤ ≤ (spMap ioO ≫ xt ≫ ρ) ⁻¹ᵁ ch.U := fun p _ => hle (h3 (Set.mem_univ (spMap ioO p)))
    have hg : ⊤ ≤ (xg ≫ πB ≫ genι Z) ⁻¹ᵁ ch.U := by
      rw [← hρ]
      exact fun p hp => hle (hxU hp)
    have hC : ⊤ ≤ (spMap io ≫ xg ≫ πB ≫ genι Z) ⁻¹ᵁ ch.U := fun p _ => hg (Set.mem_univ (spMap io p))
    have h6 := norm_tanEv_le_one Z.t hsep hx0 hO hC ch.isFrame (b2.1 i).1 hδ1 h5 b
    have hv := ((ht.1 V f hf _ xg hxU _ h1).1 i).1
    rw [GlobalTheory.LocM.tanEv_baseChange _ _ _ Z.t _ _ ch.U hg _ hv _ io _ hC, ← hA _ xg hxU hx i hv hg b] at h6
    exact (hio _).1 h6
  choose A₀ hA₀ using key
  exact ⟨Matrix.of A₀, Matrix.ext hA₀⟩

end GlobalTheory.LieFilt.Reg
