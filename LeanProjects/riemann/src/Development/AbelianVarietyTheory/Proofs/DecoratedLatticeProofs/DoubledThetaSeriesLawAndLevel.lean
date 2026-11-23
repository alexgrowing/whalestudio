import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationa
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaSeriesLaw

open Filter Topology
open scoped TensorProduct

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)

def bt (x y : Mx D T.rank ρ) : AF D.host.F := symplOH S T (d.extX T x) (d.extY T y)

theorem bt_add_left (x x' y : Mx D T.rank ρ) : bt d T (x + x') y = bt d T x y + bt d T x' y := by
  rw [bt, map_add, GlobalTheory.OrientedHeis.symplOH_add_left]; rfl

theorem bt_add_right (x y y' : Mx D T.rank ρ) : bt d T x (y + y') = bt d T x y + bt d T x y' := by
  rw [bt, map_add, GlobalTheory.OrientedHeis.symplOH_add_right]; rfl

theorem bt_zero_right (x : Mx D T.rank ρ) : bt d T x 0 = 0 := by
  rw [bt, map_zero, GlobalTheory.FinTranslate.symplOH_zero_right]

theorem symplO_bt (x y : Mx D T.rank ρ) : symplO S T (d.extX T x) (d.extY T y) = bt d T x y + bt d T x y := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  unfold bt symplOH
  linear_combination (-symplO S T (d.extX T x) (d.extY T y)) * h2

theorem psi_bt_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (ξ η : Matrix (Fin T.rank) (Fin ρ) D.host.E) : ψ (bt d T (rat ξ) (rat η)) = 1 := by
  obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D S T (ξ * d.qX) (η * d.qY)
  rw [ratW_eq, ratW_eq, rat_mul, rat_mul] at ha
  have : bt d T (rat ξ) (rat η) = algebraMap D.host.F (AF D.host.F) (1 / 2 * a) := by
    rw [map_mul, ← ha]; rfl
  rw [this]; exact hψ.2.2.1 _

theorem symplOH_coord (h0 : d.j0 = 0) (w w' : WO S T) :
    symplOH S T w w' = bt d T (w ⬝ d.jX) (w' ⬝ d.jY) - bt d T (w' ⬝ d.jX) (w ⬝ d.jY) := by
  have h : ∀ w : WO S T, w = d.extX T (w ⬝ d.jX) + d.extY T (w ⬝ d.jY) := fun w => by
    have := (d.coordS T).left_inv w
    change d.extX T (w ⬝ d.jX) + d.ext0 T (w ⬝ d.j0) + d.extY T (w ⬝ d.jY) = w at this
    rw [h0, Matrix.mul_zero, map_zero, add_zero] at this
    exact this.symm
  conv_lhs => rw [h w, h w']
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    d.symplOH_extX_extX, d.symplOH_extY_extY, symplOH_skew S T (d.extX T (w' ⬝ d.jX)), zero_add, add_zero,
    sub_eq_add_neg]
  rfl

theorem map_mul_zero {R : Type} [CommRing R] (q : AE D →+* R) {l m n : ℕ} {x : Mx D l m} (hx : x.map q = 0)
    (y : Mx D m n) : (x ⬝ y : Mx D l n).map q = 0 := by
  rw [Matrix.map_mul, hx, Matrix.zero_mul]

theorem snd_bt {x : Mx D T.rank ρ} (hx : x.map (finPart D) = 0) (y : Mx D T.rank ρ) : (bt d T x y).2 = 0 := by
  have h := GlobalTheory.OrientedHeis.snd_symplO (S := S) (T := T) (x := d.extX T x) (y := d.extY T y)
    (Or.inl (map_mul_zero _ hx _))
  change _ * sndA D.host.F (symplO S T (d.extX T x) (d.extY T y)) = 0
  rw [h, mul_zero]

theorem bt_eq_pair (x : Mx D T.rank ρ) {y : Mx D T.rank ρ} (hy : y.map (infPart D) = 0) :
    bt d T x y = pairA D.host.F 0 (bt d T x y).2 := by
  have h := GlobalTheory.OrientedHeis.fst_symplO (S := S) (T := T) (x := d.extX T x) (y := d.extY T y)
    (Or.inr (map_mul_zero _ hy _))
  refine Prod.ext ?_ rfl
  change _ * fstA D.host.F (symplO S T (d.extX T x) (d.extY T y)) = 0
  rw [h, mul_zero]

theorem exists_section (D : D7) : ∃ s : Af D.host.F ⊗[D.host.F] D.host.E → AE D, Continuous s ∧
    ∀ z, finPart D (s z) = z := by
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨fun z => e.symm (0, z), hc.comp (continuous_const.prodMk continuous_id), fun z => ?_⟩
  have := (he (e.symm (0, z))).2
  rw [e.apply_symm_apply] at this
  exact this.symm

theorem exists_open_ann {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (Z : Set (Mx D T.rank ρ))
    {K : Set (Matrix (Fin T.rank) (Fin ρ) (Af D.host.F ⊗[D.host.F] D.host.E))} (hK : IsCompact K)
    (hZ : ∀ z ∈ Z, z.map (finPart D) ∈ K) :
    ∃ V : AddSubgroup (Mx D T.rank ρ), IsOpen (V : Set (Mx D T.rank ρ)) ∧
      ∀ b ∈ V, b.map (infPart D) = 0 → ∀ z ∈ Z, ψ (bt d T z b) = 1 := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨s, hs, hsf⟩ := exists_section D
  have hadd : ∀ z a b, ψ (pairA D.host.F 0 (bt d T z (a + b)).2) =
      ψ (pairA D.host.F 0 (bt d T z a).2) * ψ (pairA D.host.F 0 (bt d T z b).2) := fun z a b => by
    rw [← AddChar.map_add_eq_mul, bt_add_right]
    congr 1
    exact Prod.ext (add_zero _).symm rfl
  have hzero : ∀ z, ψ (pairA D.host.F 0 (bt d T z 0).2) = 1 := fun z => by
    rw [bt_zero_right]; exact ψ.map_zero_eq_one
  let V : AddSubgroup (Mx D T.rank ρ) :=
    { carrier := {b | ∀ z ∈ Z, ψ (pairA D.host.F 0 (bt d T z b).2) = 1}
      zero_mem' := fun z _ => hzero z
      add_mem' := fun {a b} ha hb z hz => by rw [hadd, ha z hz, hb z hz, one_mul]
      neg_mem' := fun {a} ha z hz => by
        have := hadd z a (-a)
        rw [add_neg_cancel, hzero, ha z hz, one_mul] at this
        exact this.symm }
  refine ⟨V, V.isOpen_of_mem_nhds (g := 0) ?_, fun b hb h0 z hz => ?_⟩
  · have hK' : IsCompact ((fun k => k.map s) '' K) := hK.image (continuous_id.matrix_map hs)
    have hc : Continuous fun p : Mx D T.rank ρ × Mx D T.rank ρ => (bt d T p.2 p.1).2 :=
      continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH (continuous_snd.matrix_mul continuous_const)
        (continuous_fst.matrix_mul continuous_const))
    have hev : ∀ᶠ b in 𝓝 (0 : Mx D T.rank ρ), ∀ z ∈ (fun k => k.map s) '' K,
        ψ (pairA D.host.F 0 (bt d T z b).2) = 1 := by
      refine hK'.eventually_forall_of_forall_eventually fun z _ => ?_
      exact hc.continuousAt.preimage_mem_nhds (x := (0, z)) (t := {a | ψ (pairA D.host.F 0 a) = 1})
        (by rw [bt_zero_right]; exact GlobalTheory.FinTranslate.ker_mem_nhds hψ.1 hψ.2.1)
    refine Filter.mem_of_superset hev fun b hb z hz => ?_
    have h1 := hb _ ⟨_, hZ z hz, rfl⟩
    have h2 : (z - (z.map (finPart D)).map s).map (finPart D) = 0 := by
      ext i j
      exact (RingHom.map_sub _ _ _).trans (sub_eq_zero.2 (hsf _).symm)
    have h3 : (bt d T z b).2 = (bt d T ((z.map (finPart D)).map s) b).2 := by
      have h4 := bt_add_left d T (z - (z.map (finPart D)).map s) ((z.map (finPart D)).map s) b
      rw [sub_add_cancel] at h4
      rw [h4]
      exact (congrArg (· + _) (snd_bt d T h2 b)).trans (zero_add _)
    rw [h3]; exact h1
  · rw [bt_eq_pair d T z h0]; exact hb z hz

variable {d T} {ψ : AddChar (AF D.host.F) ℂ} {φ : Mx D T.rank ρ → ℂ} {f : WO S T → ℂ}

theorem addChar_theta_law_rearrangement_identity {R : Type} [AddCommGroup R] (χ : AddChar R ℂ) (a b c e g h : R) (t : ℂ) (ha : χ a = 1) (hg : χ g = 1) :
    χ (-(a + b + (c + e))) * (χ (c + e + (g + h) + (c + e + (g + h))) * t) =
      χ (-(b - c)) * χ (-e) * (χ (e + h + (e + h)) * t) := by
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [← one_mul (χ _ * χ _ * χ _), ← hg, ← one_mul (χ _ * (χ _ * χ _ * χ _)), ← hg, ← one_mul (χ (-_) * χ _), ← ha]
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  abel

theorem law (hψ : IsCharAF D.host.F ψ) (h0 : d.j0 = 0)
    (hf : ∀ w : WO S T, f w = ψ (-(bt d T (w ⬝ d.jX) (w ⬝ d.jY))) * ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
      ψ (symplO S T (d.extX T (w ⬝ d.jX + rat ξ)) (d.extY T (w ⬝ d.jY))) * φ (w ⬝ d.jX + rat ξ))
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T) :
    f (rat γ + w) = ψ (-(symplOH S T (rat γ) w)) * f w := by
  have hX : (rat γ ⬝ d.jX : Mx D T.rank ρ) = rat (γ * d.e) := (rat_mul _ _).symm
  have hY : (rat γ ⬝ d.jY : Mx D T.rank ρ) = rat (γ * d.e') := (rat_mul _ _).symm
  rw [hf, hf, symplOH_coord d T h0, Matrix.add_mul, Matrix.add_mul, hX, hY]
  generalize γ * d.e = ξ₀
  generalize γ * d.e' = η₀
  generalize (w ⬝ d.jX : Mx D T.rank ρ) = x
  generalize (w ⬝ d.jY : Mx D T.rank ρ) = y
  rw [← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
  refine Eq.trans (tsum_congr fun ξ => ?_) ((Equiv.addLeft ξ₀).tsum_eq _)
  have e : rat ξ₀ + x + rat ξ = x + rat (Equiv.addLeft ξ₀ ξ) := by
    rw [Equiv.coe_addLeft, rat_add]; abel
  rw [e]
  generalize Equiv.addLeft ξ₀ ξ = ζ
  have h1 := psi_bt_rat d T hψ ξ₀ η₀
  have h2 := psi_bt_rat d T hψ ζ η₀
  simp only [symplO_bt, bt_add_left]
  simp only [bt_add_right]
  exact addChar_theta_law_rearrangement_identity ψ _ _ _ _ _ _ _ h1 h2

theorem level (hψ : IsCharAF D.host.F ψ) (h0 : d.j0 = 0) (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ)
    (hf : ∀ w : WO S T, f w = ψ (-(bt d T (w ⬝ d.jX) (w ⬝ d.jY))) * ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
      ψ (symplO S T (d.extX T (w ⬝ d.jX + rat ξ)) (d.extY T (w ⬝ d.jY))) * φ (w ⬝ d.jX + rat ξ)) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  obtain ⟨K, hK, hKφ⟩ := hφ.supp
  obtain ⟨V, hV, hVψ⟩ := exists_open_ann d T hψ {z | φ z ≠ 0} hK hKφ
  let rX : WO S T →+ Mx D T.rank ρ := AddMonoidHom.mk' (fun w => w ⬝ d.jX) fun _ _ => Matrix.add_mul _ _ _
  let rY : WO S T →+ Mx D T.rank ρ := AddMonoidHom.mk' (fun w => w ⬝ d.jY) fun _ _ => Matrix.add_mul _ _ _
  have cX : Continuous rX := continuous_id.matrix_mul continuous_const
  have cY : Continuous rY := continuous_id.matrix_mul continuous_const
  refine ⟨U.comap rX ⊓ V.comap rY, (hU.preimage cX).inter (hV.preimage cY), fun u hu hi => ?_⟩
  have ha := hUφ (u ⬝ d.jX) hu.1 (map_mul_zero _ hi _)
  have hb := hVψ (u ⬝ d.jY) hu.2 (map_mul_zero _ hi _)
  funext w
  rw [heisO, hf, hf, symplOH_coord d T h0, Matrix.add_mul, Matrix.add_mul]
  generalize (u ⬝ d.jX : Mx D T.rank ρ) = a at ha ⊢
  generalize (u ⬝ d.jY : Mx D T.rank ρ) = b at hb ⊢
  generalize (w ⬝ d.jX : Mx D T.rank ρ) = x
  generalize (w ⬝ d.jY : Mx D T.rank ρ) = y
  rw [← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  rw [add_right_comm x a, ha]
  generalize x + rat ξ = z
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero]
  have h1 := hb z hz
  have h2 := hb (z + a) (by rwa [Set.mem_setOf_eq, ha])
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [← one_mul (ψ (-bt d T x y) * ψ _), ← h1, ← one_mul (ψ (bt d T z b) * _), ← h2]
  simp only [← AddChar.map_add_eq_mul, symplO_bt, bt_add_left, bt_add_right]
  congr 1
  abel

theorem law_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → (∀ γ w, f (ratW B (dblSp A) γ + w) = ψ (-(symplOH (dblSp A) B (ratW B (dblSp A) γ) w)) * f w) ∧ ∃ U : AddSubgroup (WO (dblSp A) B), IsOpen (U : Set (WO (dblSp A) B)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ (dblSp A) B u f = f := by
  intro D ψ hψ A B φ hφ f hf
  have h0 : (dblDec A).j0 = 0 := rat_zero
  exact ⟨law hψ.1 h0 hf, level hψ.1 h0 hφ hf⟩

end GlobalTheory.ThetaSeriesLaw

end
