import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InputExistsOfMemberExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.Reindex

attribute [local instance] Over.cartesianMonoidalCategory

variable {g g' : ℕ}

noncomputable def rho (ε : Fin g' ≃ Fin g) : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε i)

theorem rho_apply (ε : Fin g' ≃ Fin g) (z : Fin g → ℂ) : rho ε z = z ∘ ε := rfl

theorem rho_single (ε : Fin g' ≃ Fin g) (m : Fin g) : rho ε (Pi.single m 1) = Pi.single (ε.symm m) 1 := by
  funext i
  rw [rho_apply, Function.comp_apply, Pi.single_apply, Pi.single_apply]
  simp only [Equiv.eq_symm_apply]

theorem rho_injective (ε : Fin g' ≃ Fin g) : Function.Injective (rho ε) := fun z w h => by
  funext i
  simpa [rho_apply] using congrFun h (ε.symm i)

theorem hermForm_reindex (ε : Fin g' ≃ Fin g) (Hm : Matrix (Fin g') (Fin g') ℂ) (z w : Fin g → ℂ) :
    hermForm (Hm.submatrix ε.symm ε.symm) z w = hermForm Hm (rho ε z) (rho ε w) := by
  unfold hermForm
  rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, dotProduct_comp_equiv_symm]
  rfl

noncomputable def rhoM (ε : Fin g' ≃ Fin g) : (Fin g → ℂ) ≃ᵐ (Fin g' → ℂ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℂ) ε).symm

theorem rhoM_eq (ε : Fin g' ≃ Fin g) : ⇑(rhoM ε) = ⇑(rho ε) := rfl

theorem rho_mp (ε : Fin g' ≃ Fin g) : MeasurePreserving (rhoM ε) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ => ℂ) ε).symm _

theorem fund_reindex (ε : Fin g' ≃ Fin g) {A A' : Type} [AddCommGroup A] [AddCommGroup A'] (ψ : A ≃ A')
    (P : A →+ (Fin g → ℂ)) (P' : A' →+ (Fin g' → ℂ)) (h : ∀ a, P' (ψ a) = rho ε (P a)) {Fd : Set (Fin g' → ℂ)}
    (hF : IsAddFundamentalDomain P'.range Fd volume) : IsAddFundamentalDomain P.range (rho ε ⁻¹' Fd) volume := by
  have key : ∀ v : P'.range, rho ε.symm v.1 ∈ P.range := by
    rintro ⟨_, b, rfl⟩
    refine ⟨ψ.symm b, rho_injective ε ?_⟩
    rw [← h, Equiv.apply_symm_apply]
    funext i
    simp [rho_apply]
  refine hF.preimage_of_equiv (f := rho ε) (rho_mp ε).quasiMeasurePreserving
    (e := fun v => ⟨rho ε.symm v.1, key v⟩) ⟨fun v w hvw => ?_, ?_⟩ fun v z => ?_
  · exact Subtype.ext (rho_injective _ (congrArg Subtype.val hvw))
  · rintro ⟨_, a, rfl⟩
    refine ⟨⟨P' (ψ a), ψ a, rfl⟩, Subtype.ext ?_⟩
    funext i
    simp [h, rho_apply]
  · funext i
    change v.1 (ε.symm (ε i)) + z (ε i) = v.1 i + z (ε i)
    rw [Equiv.symm_apply_apply]

open MonObj in
theorem left_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {y y' : Sp ℂ ⟶ S} (hy : y = y')
    (ρ : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ))
    {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} {e' : (Fin g' → ℂ) → (Over.mk y' ⟶ G)}
    (he : ∀ z w, e (z + w) = e z * e w) (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (ρ (Pi.single i 1)) (u i)) (z : Fin g → ℂ) :
    (e z).left = (e' (ρ z)).left := by
  subst hy
  have E : e = fun z => e' (ρ z) :=
    GlobalTheory.CuspFamilyCompare.exp_unique he (fun z w => by rw [map_add, he']) hol
      (HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
        (HolHom.holAt_of_isHolTo hol' (Set.mem_univ (ρ z))).precomp ρ.differentiableAt)
      u hd (fun m => GlobalTheory.CuspFamilyCompare.isDerivAt0_comp hol' ρ (hd' m))
  rw [E]

end GlobalTheory.FrameEquiv.Reindex

namespace GlobalTheory.FrameEquiv

open Reindex

set_option maxHeartbeats 1000000 in

theorem hasWitness_of_is : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (d : GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.DictDat U), d.Is W hr dict ι x₀ → HasWitness d := by
  intro D H Dw l Xo c σ r U _ hU _ W hr dict ι x₀ d hd
  obtain ⟨W₀⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU)
  obtain ⟨-, ⟨hiso, hpt⟩, -⟩ := hd
  refine ⟨⟨d.g, d.e, d.F, d.ik, d.φ, hiso, fun k x => ?_⟩, rfl⟩
  obtain ⟨Pm, h1, h2, h3, h4⟩ := hpt k x
  refine ⟨Pm, h1, h2, h3, h4, fun hun => ?_⟩
  obtain ⟨Pm', b1, b2, b3, b4, b5⟩ := W₀.pt k x
  obtain ⟨Hm, χl, fr, θ, Fd, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := b5 hun
  let ε : Fin W₀.g ≃ Fin d.g := W₀.e.trans d.e.symm
  let ψ : (d.F.Di (d.ik k)).La ≃ (W₀.F.Di (W₀.ik k)).La := ((d.φ k).trans (W₀.φ k).symm).toEquiv
  have hψ : ∀ a, W₀.φ k (ψ a) = d.φ k a := fun a => (W₀.φ k).apply_symm_apply _
  have hP : ∀ a, Pm' (ψ a) = rho ε (Pm a) := fun a => by
    funext j
    have hj : d.e (ε j) = W₀.e j := d.e.apply_symm_apply _
    rw [rho_apply, Function.comp_apply, h1, b1, hψ, hj]
    rfl
  have hE : ∀ z, (d.F.ex (d.ik k) Pm z).left = (W₀.F.ex (W₀.ik k) Pm' (rho ε z)).left :=
    left_eq (h3.symm.trans b3) (rho ε) (d.F.ex_add _ _ h2) (W₀.F.ex_add _ _ b2)
      (GlobalTheory.CuspFamilyCompare.isHolTo_ex _ _ h2) (GlobalTheory.CuspFamilyCompare.isHolTo_ex _ _ b2)
      (fun m => (U.un k x).u (d.e m).1 (d.e m).2)
      (fun m => by simpa using h4 (d.e m).1 (d.e m).2)
      (fun m => by rw [rho_single]; exact b4 (d.e m).1 (d.e m).2)
  refine ⟨Hm.submatrix ε.symm ε.symm, fun z => χl (rho ε z), fun j z => fr j (rho ε z), fun z => θ (rho ε z),
    rho ε ⁻¹' Fd, c1.submatrix _, fun z hz => ?_, fun a b => ?_, fun j => ?_, fun j z hz => ?_, fun j j' z hz => ?_,
    fun j hz => ?_, fun a j z => ?_, fun j z pt p1 p2 hz => ?_, fund_reindex ε ψ Pm Pm' hP c10, ?_⟩
  · rw [hermForm_reindex]
    exact c2 _ fun h0 => hz (rho_injective ε (h0.trans (map_zero _).symm))
  · rw [hermForm_reindex, ← hP, ← hP, c3]
    have := (W₀.isom k (ψ a) (ψ b))
    rw [hψ, hψ] at this
    exact_mod_cast this.trans (hiso k a b).symm
  · refine (c4 j).comp (rho ε).differentiable.differentiableOn fun z hz => ?_
    rw [Set.mem_ofPred_eq, hE] at hz
    exact hz
  · rw [hE] at hz
    exact c5 _ _ hz
  · rw [hE] at hz ⊢
    exact c6 _ _ _ hz
  · rw [hE, map_zero] at hz
    simp only [map_zero]
    exact c7 _ hz
  · simp only [hermForm_reindex, map_add, ← hP, hE]
    exact c8 _ _ _
  · rw [hE] at hz p1
    exact c9 _ _ _ p1 p2 hz
  · simp only [hermForm_reindex]
    have m1 : volume (rho ε ⁻¹' Fd) = volume Fd := (rho_mp ε).measure_preimage_equiv Fd
    have m2 := (rho_mp ε).setIntegral_preimage_emb (rhoM ε).measurableEmbedding
      (fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) Fd
    rw [m1]
    exact (congrArg (· / _) m2).trans c11

end GlobalTheory.FrameEquiv
