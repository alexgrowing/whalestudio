import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.OmegaHT (crd ToOpen)
open GlobalTheory.FieldPtGlue GlobalTheory.ShFam.Pad.Pull GlobalTheory.LieMet
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChainPts.SysB.FormAct

theorem crd_app {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {V V' : X.Opens} {s : Fin r → Γ(F, V')} (hs : GlobalTheory.VB.IsFrame s)
    (u : F ⟶ F) (c : Fin r → Γ(X, V')) (hu : ∀ i, u.app V' (s i) = c i • s i) (σ : Γ(F, V)) (i : Fin r) :
    crd hs (u.app V σ) i = resG X inf_le_right (c i) * crd hs σ i := by
  have e : resM F (inf_le_left : V ⊓ V' ≤ V) (u.app V σ) =
      ∑ j, (resG X inf_le_right (c j) * crd hs σ j) • hs.basis (inf_le_right : V ⊓ V' ≤ V') j := by
    rw [← app_resM, ← (hs.basis (inf_le_right : V ⊓ V' ≤ V')).sum_repr (resM F inf_le_left σ)]
    simp only [map_sum, Scheme.Modules.Hom.app_smul, GlobalTheory.VB.IsFrame.basis_apply, app_resM, hu, resM_smul, smul_smul]
    exact Finset.sum_congr rfl fun j _ => congrArg (· • resM F inf_le_right (s j)) (mul_comm _ _)
  rw [crd, e, Module.Basis.repr_sum_self]

theorem spMap_epsMul_one (k : Type) [CommRing k] : spMap (epsMul (1 : k)) = 𝟙 _ := by
  have : epsMul (1 : k) = RingHom.id _ := by ext z <;> simp [epsMul]
  rw [this]
  exact Spec.map_id _

section Tan

open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open scoped MonObj

theorem exists_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {X : Scheme.{0}} {t : SAB H X} {l : Level H} {c : Coeff l} {k : Type} [Field k] {y : Sp k ⟶ X} {r : ℕ}
    {x : Fin r → Letter Dw} {f : c.F →+* k} {u : Vecs Dw t k} (hu : GlobalTheory.LocM.IsFrame t f y u) (hx : Function.Bijective x)
    {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t y v) :
    ∃ cf, IsCombAtG t y (fun i => u (x i).1 (x i).2) cf v := by
  let U : Fin r → TanM y t.G := fun i => tanOf (hu.1 (x i).1 (x i).2).1
  let e := Equiv.ofBijective x hx
  obtain ⟨d, hd, -⟩ := GlobalTheory.TanSec.Frame.exists_unique_coords hu (tanOf hv)
  have key : ∑ i, d (e i) • U i = ∑ q, d q • tanOf (hu.1 q.1 q.2).1 :=
    e.sum_comp fun q => d q • tanOf (hu.1 q.1 q.2).1
  exact ⟨fun i => d (e i), (comb_iff U _ _).2 (congrArg (fun m => (tv m).left) (hd.trans key.symm))⟩

end Tan

theorem formActSt : FormActSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z O _ _ _ B h r x hx hopn F s k U t φt hφt hact lam hl a σ v v' hv'
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.TestPts.exists_chart_of_maximal h hopn (η := genericPoint B.X) fun y hy =>
    (hy.antisymm ((genericPoint_spec B.X).specializes (Set.mem_univ y))).eq
  let κ : U.Bp →+* GlobalTheory.GroupBplus.Kbar B.X := algebraMap _ _
  have hκ : Function.Injective κ := Subtype.val_injective
  have hw : ⊤ ≤ (spMap κ ≫ U.toX) ⁻¹ᵁ (U.1 ⊓ h ⁻¹ᵁ (Z.U a₀).1) := by
    rw [U.val_toX]
    intro q _
    have hg : genericPoint B.X ∈ U.1 := ((genericPoint_spec B.X).mem_open_set_iff U.1.isOpen).2 (by simpa using U.2.2)
    have hq : GlobalTheory.GroupBplus.genPt B.X q ⤳ genericPoint B.X := by
      have : GlobalTheory.GroupBplus.genPt B.X q ∈ Set.range (B.X.fromSpecStalk (genericPoint B.X)) :=
        ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact hq.mem_open (U.1 ⊓ h ⁻¹ᵁ (Z.U a₀).1).isOpen ⟨hg, ha₀⟩
  obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a₀).2 ((spMap κ ≫ U.toX) ≫ h) fun q hq => (hw hq).2
  have hφ' : spMap φ ≫ Z.chart a₀ = spMap κ ≫ U.toX ≫ h := hφ.trans (Category.assoc ..)
  have f := chart_frame Z (a := a₀) hφ'
  simp only [Category.assoc] at f
  have hT := isTan_map κ rfl (GlobalTheory.LocM.TanPair.isTanAtG_lieG hφt v)
  obtain ⟨cf, hcf⟩ := exists_coeff f hx hT
  have h₂ := (GlobalTheory.OmegaHT.Transpose.comb_op f hcf 1 (H.bar a)).2
  rw [spMap_epsMul_one, Category.id_comp] at h₂
  have e : (spMap (dualMap κ) ≫ v.1.left ≫ φt) ≫ ((Y Z.i).t.act.act (H.bar a)).left =
      spMap (dualMap κ) ≫ v'.1.left ≫ φt := by
    rw [hv', Over.comp_left, Category.assoc, Category.assoc, Category.assoc, hact]
  rw [e] at h₂
  apply hκ
  rw [hl _ v _ κ a₀ φ hφ' cf hcf, hl _ v' _ κ a₀ φ hφ' _ h₂]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e₁ := crd_app (k.2.2.1.frame a₀) (F.ρ a : F.V ⟶ F.V) (fun i => GlobalTheory.OmegaHT.Transpose.eig h 1 (H.bar a) a₀ (x i))
    (fun i => by rw [GlobalTheory.OmegaHT.Transpose.eig, map_one, one_mul]; exact k.2.2.2 a₀ i a) σ i
  obtain ⟨ev, hev⟩ := GlobalTheory.ChainPts.LatUniq.exists_ev (le_top.trans (le_refl _) : ⊤ ≤ (spMap κ ≫ U.toX) ⁻¹ᵁ ⊤)
  rw [e₁, valF_mul hw, GlobalTheory.OmegaHT.Transpose.valF_eig 1 _ _ hφ _ hw, hev, map_one]
  exact (mul_assoc _ _ _).symm

end GlobalTheory.ChainPts.SysB.FormAct

end
