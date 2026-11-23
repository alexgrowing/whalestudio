import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv TanM)
open GlobalTheory.LieMet (tanOf isTan_tv tan_ext pushE left_pushE)

namespace GlobalTheory.LocM.LatCover

theorem exists_coordEquiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L g hg V n m hm k _ x h hx τ mu hπ
  have hgen : ⊤ ≤ (x ≫ g) ⁻¹ᵁ B.genO := by
    intro z _
    have hz : x z ∈ Z.genO := CommonMod.mem_genO_of_mem_opn hp.ne_zero Z (hx ⟨z, rfl⟩)
    rw [← CommonMod.preimage_genO g] at hz
    exact hz
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ (V ⊓ B.genO) := fun z hz => ⟨h hz, hgen hz⟩
  let m' : Fin n → Γ(GlobalTheory.LieVB.omega B.t.G, V ⊓ B.genO) :=
    fun l => GlobalTheory.Twist.resM _ inf_le_left (L.N.incl.app V (m l))
  have hm' : GlobalTheory.VB.IsFrame m' := by
    refine (hm.res (inf_le_left : V ⊓ B.genO ≤ V)).map_of_linearEquiv
      (fun U hU => LinearEquiv.ofBijective (GlobalTheory.QCoh.appLinear L.N.incl U)
        ⟨L.N.incl_app_injective U, fun s => L.N.mem_sec_iff.1 (by
          rw [L.gen U (hU.trans inf_le_right)]
          trivial)⟩) fun U hU i => ?_

    show L.N.incl.app U (GlobalTheory.Twist.resM _ hU (GlobalTheory.Twist.resM _ inf_le_left (m i))) =
      GlobalTheory.Twist.resM _ hU (GlobalTheory.Twist.resM _ inf_le_left (L.N.incl.app V (m i)))
    rw [GlobalTheory.Twist.app_resM, GlobalTheory.Twist.app_resM]
  have tcomb : ∀ (r : ℕ) (u : Fin r → TanM (x ≫ g) B.t.G) (a : Fin r → k) (l : Fin n),
      tanEv B.t (isTan_tv (∑ i, a i • u i)) h' (m' l) = ∑ i, a i * tanEv B.t (isTan_tv (u i)) h' (m' l) :=
    fun r u a l => GlobalTheory.LocM.tanEv_comb E H B.X B.t k (x ≫ g) _ h' r (fun i => (tv (u i)).left)
      (fun i => isTan_tv (u i)) a _ (isTan_tv _) ((GlobalTheory.LieMet.isComb_iff u a _).2 rfl) (m' l)
  let ev : TanM (x ≫ g) B.t.G →ₗ[k] (Fin n → k) :=
    { toFun := fun v l => tanEv B.t (isTan_tv v) h' (m' l)
      map_add' := fun v w => funext fun l => by
        have e := tcomb 2 ![v, w] ![1, 1] l
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, _root_.one_mul] at e
        exact e
      map_smul' := fun c v => funext fun l => by
        have e := tcomb 1 ![v] ![c] l
        simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at e
        exact e }
  have hev : Function.Bijective ev := by
    constructor
    · intro v w hvw
      have u := (GlobalTheory.TanFibre.existsUnique_tanEv E H B.X B.t k (x ≫ g) _ h' n m' hm' (ev v)).unique
        ⟨isTan_tv v, fun l => rfl⟩ ⟨isTan_tv w, fun l => (congrFun hvw l).symm⟩
      exact tan_ext u
    · intro c
      obtain ⟨u, ⟨hu, hval⟩, -⟩ := GlobalTheory.TanFibre.existsUnique_tanEv E H B.X B.t k (x ≫ g) _ h' n m' hm' c
      exact ⟨tanOf hu, funext hval⟩
  have hB : (x ≫ g) ≫ B.π = (x ≫ Z.π) ≫ τ := by
    rw [Category.assoc, Category.assoc, hπ]
  refine ⟨(pushE mu (x ≫ Z.π) rfl).trans ((pushE B.tMap (x ≫ g) hB).symm.trans (LinearEquiv.ofBijective ev hev)),
    fun w => ⟨_, isTan_tv ((pushE B.tMap (x ≫ g) hB).symm (pushE mu (x ≫ Z.π) rfl w)), ?_, fun l => ?_⟩⟩
  · rw [← left_pushE B.tMap (x ≫ g) hB, LinearEquiv.apply_symm_apply]
    rfl
  · exact (GlobalTheory.LocM.tanEv_resM B.t _ h' inf_le_left _).symm

end GlobalTheory.LocM.LatCover
