import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticFibreDescriptionUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces

namespace GlobalTheory.OneMapRef.DictPt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem isDerivAt0_comp {X : Scheme.{0}} {g g' : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (hol : IsHolTo Set.univ e)
    (ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ} {u : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt0 e (ρ w) u) :
    IsDerivAt0 (fun z => e (ρ z)) w u := by
  rw [HolHom.isDerivAt0_iff] at h ⊢
  refine ⟨h.1.trans (congrArg e (map_zero ρ).symm), fun U hU f => ?_⟩
  have hU' : ⊤ ≤ e 0 ⁻¹ᵁ U := by simpa only [map_zero] using hU
  have h1 : HasFDerivAt (fun t => valAt' (e t) U f) (fderiv ℂ (fun t => valAt' (e t) U f) 0) (ρ 0) := by
    rw [map_zero]; exact ((HolHom.holAt_of_isHolTo hol (Set.mem_univ 0) U hU').2 f).hasFDerivAt
  exact (h.2 U hU' f).trans (congrArg (· w) (h1.comp 0 ρ.hasFDerivAt).fderiv).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g g' : ℕ} {ty : Fin g' → (E →+* ℂ)}

theorem isHolTo_ex (F : FamilyUnif Xo σ ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g' → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) : IsHolTo Set.univ (fun z => (F.ex i P z).left) := by
  have h := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
    (HolHom.holAt_of_isHolTo h (z := (0, z)) ⟨trivial, trivial⟩).precomp (k := fun z => (0, z)) (by fun_prop)

theorem levPt_eq (F : FamilyUnif Xo σ ty) (i : Fin F.n) {Pm : (F.Di i).La →+ (Fin g' → ℂ)}
    (hper : IsPeriod (F.Di i) ty Pm) (π : Fin g ≃ Fin g') {y : Sp ℂ ⟶ Xo.X} (h : y = F.u i Pm)
    (ex : (Fin g → ℂ) → (ptO Xo y ⟶ Xo.univ.t.G)) (u : Fin g' → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (b1 : ∀ z w, ex (z + w) = ex z * ex w) (b2 : IsHolTo Set.univ (fun z => (ex z).left))
    (b3 : ∀ m, IsDerivAt0 (fun z => (ex z).left) (Pi.single (π.symm m) 1) (u m))
    (b4 : ∀ m, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single m 1) (u m))
    (a : Dw.La) (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) :
    levPt Xo y a = ex (fun j => (l.M : ℂ)⁻¹ * Pm (F.t i a) (π j)) := by
  subst h
  let ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (π j)
  have hρ : ∀ m, ρ (Pi.single m 1) = Pi.single (π.symm m) 1 := fun m => by
    funext j
    change (Pi.single m 1 : Fin g' → ℂ) (π j) = _
    simp only [Pi.single_apply, Equiv.eq_symm_apply]
  have E : (fun z => ex (ρ z)) = F.ex i Pm :=
    GlobalTheory.AnUniq.exp_eq (fun z w => by rw [map_add, b1]) (F.ex_add _ _ hper)
      (HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
        (HolHom.holAt_of_isHolTo b2 (Set.mem_univ (ρ z))).precomp ρ.differentiableAt) (isHolTo_ex F _ hper)
      u (fun m => isDerivAt0_comp b2 ρ (by rw [hρ]; exact b3 m)) b4
  exact (F.ex_eta i Pm hper a ha).trans (congrFun E _).symm

theorem ex_add_ker {y : Sp ℂ ⟶ Xo.X} (ex : (Fin g → ℂ) → (ptO Xo y ⟶ Xo.univ.t.G))
    (b1 : ∀ z w, ex (z + w) = ex z * ex w) (z k z' : Fin g → ℂ) (hk : ex k = 1) (h : z' = z + k) : ex z = ex z' := by
  rw [h, b1, hk, _root_.mul_one]

theorem sub_eq_nsmul {A : Type} [AddCommGroup A] (M : ℕ) (p q z w w' : A) (e : p - z = M • w)
    (e' : q - z = M • w') : p - q = M • (w - w') := by
  rw [smul_sub, ← e, ← e', sub_sub_sub_cancel_right]

end GlobalTheory.OneMapRef.DictPt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

theorem GlobalTheory.OneMapRef.DictPt.exists_sub_eq {D : D7} (V : HSp D) (g : GA D V) (M : ℕ) (hM : M ≠ 0)
    (p q : Fin V.rank → D.host.E) (z w w' : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : w ∈ latGHat V g) (hw' : w' ∈ latGHat V g) (e : finVec V p - z = M • w) (e' : finVec V q - z = M • w') :
    (M : D.host.E)⁻¹ • (p - q) ∈ latG V g := by
  rw [(GlobalTheory.MarkCoset.latG_spec D V g).1]
  have hM' : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have h1 : M • finVec V ((M : D.host.E)⁻¹ • (p - q)) = M • (w - w') := by
    refine Eq.trans ?_ (GlobalTheory.OneMapRef.DictPt.sub_eq_nsmul M _ _ z w w' e e')
    funext i
    change M • ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((M : D.host.E)⁻¹ * (p i - q i))) = 1 ⊗ₜ p i - 1 ⊗ₜ q i
    rw [← TensorProduct.tmul_smul, nsmul_eq_mul, mul_inv_cancel_left₀ hM', TensorProduct.tmul_sub]
  have h2 : finVec V ((M : D.host.E)⁻¹ • (p - q)) = w - w' :=
    GlobalTheory.MarkCoset.nsmul_cancel D.host.F M (Nat.cast_ne_zero.2 hM) h1
  rw [h2]
  exact sub_mem hw hw'

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.OneMapRef.DictPt.dict_point : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (r : ℕ) (hr : W.rank = r) (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g₀ : ℕ) (e₀ : Fin g₀ ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e₀ j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (θ : InfFam D) (Z₀ : Fam W), GoodEmb c σ → IsUnf U → 1 ≤ r → IsInfFam θ → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e₀ F ik φ th x₀ → (∀ ρ, x₀ (tauE D ρ) = Matrix.reindex (finCongr hr) (finCongr hr) (Z₀ ρ)) → ∀ h : GA D W, ∃ γ ∈ GQ W, MarkBy U W hr dict ι F ik φ h γ ∧ latW hr (U.X (dict h).1).Λ = latG W (γ * h) ∧ (∀ eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ, (∀ ρ, (eT ρ).1 = tauE D ρ) → (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀)) ∧ ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas → Matched c σ (U.X (dict h).1) idx e → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩)) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), (∀ a, mk a ∈ (U.X (dict h).1).Λ) → MarkAd hr l ι (γ * h) mk → A.Marked mk := by
  intro D H Dw l Xo c σ W r hr U dict ι g₀ e₀ F ik φ th x₀ θ Z₀ hσ hU h1 hθ hth hD hx₀ h
  subst hr
  obtain ⟨γ, hγ, hl, hm, hf⟩ := hD.2 h
  have hΛ : (U.X (dict h).1).Λ = latG W (γ * h) := SetLike.ext' (hl.trans (Set.image_id _))
  refine ⟨γ, hγ, ⟨hγ, hl, hm⟩, hΛ, fun eT heT => ?_, ?_⟩
  · funext τ
    obtain ⟨ρ, rfl⟩ := eT.surjective τ
    have e1 : th _ (eT ρ) = θ ρ :=
      GlobalTheory.SmoothForms.RealPts.infEmb_unique _ _ _ (hth _ (eT ρ)) (by rw [heT]; exact hθ ρ)
    have := hf (eT ρ)
    rw [e1, heT, hx₀] at this
    funext a b
    simp only [frOf, Equiv.symm_apply_apply]
    exact congrFun (congrFun this a) b
  · intro hx g bas idx e hs hM
    letI : Algebra c.F ℂ := σ.toAlgebra
    intro A mk hmk hA a ha
    obtain ⟨Pm, hPm, hP, hu, hder⟩ := hD.1.2 (dict h).1 ⟨(dict h).2, hx⟩
    have hM0 : l.M ≠ 0 := by have := l.three_le; omega
    have key := GlobalTheory.OneMapRef.DictPt.levPt_eq F _ hP (e.trans e₀.symm) hu A.ex (fun m => (U.un _ ⟨(dict h).2, hx⟩).u (e₀ m).1 (e₀ m).2)
      A.ex_add A.hol (fun m => A.der (e₀ m)) (fun m => by simpa only [Sigma.eta, Equiv.symm_apply_apply] using hder (e₀ m).1 (e₀ m).2) a ha
    obtain ⟨w, hw, ew⟩ := hA a ha
    obtain ⟨w', hw', ew'⟩ := hm a ha
    have hmem := GlobalTheory.OneMapRef.DictPt.exists_sub_eq W (γ * h) l.M hM0 _ _ _ w w' hw hw' ew ew'
    rw [← hΛ] at hmem
    have hk := (A.ex_ker _).2 ⟨_, hmem, rfl⟩
    refine key.trans (GlobalTheory.OneMapRef.DictPt.ex_add_ker A.ex A.ex_add _ _ _ hk ?_)
    funext j
    have e3 : ∀ v (ℓ ℓ' : Lt1 Dw), ℓ = ℓ' → perFr (U.X (dict h).1) (dict h).2 v (relab c σ ℓ.1) ℓ.2 =
        perFr (U.X (dict h).1) (dict h).2 v (relab c σ ℓ'.1) ℓ'.2 := fun v ℓ ℓ' hℓ => by rw [hℓ]
    rw [Pi.add_apply, hPm, Equiv.trans_apply, e3 _ _ _ (e₀.apply_symm_apply (e j)), ← hM.1]
    have e2 : ∀ p q : Fin W.rank → D.host.E, (l.M : D.host.E)⁻¹ • p =
        (l.M : D.host.E)⁻¹ • q + (l.M : D.host.E)⁻¹ • (p - q) := fun p q => by rw [← smul_add, add_sub_cancel]
    rw [e2 (mk a) (φ _ (F.t _ a))]
    simp only [pv, Function.comp_apply, per_add, Pi.add_apply]
    congr 1
    rw [per_smul, map_inv₀, map_natCast]
