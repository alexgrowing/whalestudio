import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaAtEqProdAhG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ColSplit

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues GlobalTheory.AdLat
open scoped TensorProduct

variable {D : D7}

theorem finite_part_apply (V W : HSp D) (Y : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (i : Fin W.rank) (j : Fin V.rank) :
    (ratW W V Y - realPt V W Y : WO V W) i j = (pairA D.host.F 0 1) ⊗ₜ[D.host.F] Y i j := by
  change (1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j - (pairA D.host.F 1 0) ⊗ₜ[D.host.F] Y i j = _
  rw [← TensorProduct.sub_tmul]
  congr 1
  exact Prod.ext (sub_self (1 : Ainf D.host.F)) (sub_zero (1 : Af D.host.F))

def rk (V W : HSp D) (s : Fin V.rank → D.host.E) : (Fin W.rank → D.host.E) →+ WO V W where
  toFun c := Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (c i * ∑ k, star (s k) * V.gram k j)
  map_zero' := by ext i j; simp
  map_add' y z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, add_mul, TensorProduct.tmul_add]

theorem rk_mem (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (L : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (s : Fin V.rank → D.host.E) (hs : s ∈ LV) (c : Fin W.rank → D.host.E)
    (hc : c ∈ Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v}) :
    rk V W s c ∈ latO V W LV (L : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have hc' := (GlobalTheory.OneMapRef.FactsLat.isAA_span L c).1 hc
  clear hc
  induction hc' using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, fun _ h => absurd trivial h, a, ha, s, hs, t, ht, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

def colF (V W : HSp D) (s : Fin V.rank → D.host.E) : WO V W →+ (Fin W.rank → RA D.host.F D.host.E) where
  toFun u := fun m => ∑ n, finPart D (u m n) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] s n)
  map_zero' := by ext m; simp
  map_add' y z := by
    ext m
    simp only [Matrix.add_apply, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem colF_pure (V W : HSp D) (s : Fin V.rank → D.host.E) (α : Af D.host.F)
    (X : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    colF V W s (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] X i j) =
      fun m => α ⊗ₜ[D.host.F] ∑ n, X m n * s n := by
  funext m
  change ∑ n, (α ⊗ₜ[D.host.F] X m n) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] s n) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.tmul_sum]

theorem colF_mem (V W : HSp D) (L : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (s : Fin V.rank → D.host.E) (hs : s ∈ GlobalTheory.Member.latC V) (u : WO V W)
    (hu : u ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) (L : Set (Fin W.rank → D.host.E)) fun _ => True) :
    colF V W s u ∈ hat D.host.F ((Submodule.span (𝓞 D.host.E)
      {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v} : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) :
        Set (Fin W.rank → D.host.E)) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, -, a, ha, s', hs', t, ht, rfl⟩ := hx
    rw [colF_pure V W s α fun i j => a * t i * ∑ k, star (s' k) * V.gram k j]
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1
      (((GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.2.2.2.2.2.2.2 s).2 hs s' hs')
    refine AddSubgroup.subset_closure ⟨α, hα, a • (r • t), Submodule.subset_span ⟨a, ha, _, L.smul_mem r ht, rfl⟩, ?_⟩
    funext m
    congr 1
    change _ = a * (algebraMap (𝓞 D.host.E) D.host.E r * t m)
    rw [hr]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
    change _ = a * (s n * V.gram k n * star (s' k) * t m)
    ring
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem complete (V : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) (n j : Fin V.rank) :
    ∑ a, b n a * ∑ k, star (b k a) * V.gram k j = if n = j then 1 else 0 := by
  have h1 : (Matrix.of fun a j => ∑ k, star (b k a) * V.gram k j) * b = 1 := by
    ext a a'
    rw [Matrix.one_apply, ← hb.1 a a', Matrix.mul_apply, Finset.sum_comm]
    simp only [Matrix.of_apply, Finset.sum_mul]
  have h3 : b * (Matrix.of fun a j => ∑ k, star (b k a) * V.gram k j) = 1 := mul_eq_one_comm.1 h1
  have h2 := congrFun (congrFun h3 n) j
  rw [Matrix.one_apply, Matrix.mul_apply] at h2
  exact h2

theorem cols_iff_moved (V W : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) (y : GA D W)
    (Y : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    (∀ a, (fun m => ∑ n, Y m n * b n a) ∈ latG W y) ↔
      (ratW W V Y - realPt V W Y : WO V W) ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (Bridge.hLat W (FWT.fin W y) : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have hbm : ∀ a, (fun i => b i a) ∈ GlobalTheory.Member.latC V := fun a => by
    rw [← SetLike.mem_coe, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, hb.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  constructor
  · intro h
    have e : (ratW W V Y - realPt V W Y : WO V W) = ∑ a, rk V W (fun i => b i a) fun m => ∑ n, Y m n * b n a := by
      ext i j
      rw [finite_part_apply, Matrix.sum_apply]
      change _ = ∑ a, (pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((∑ n, Y i n * b n a) * ∑ k, star (b k a) * V.gram k j)
      rw [← TensorProduct.tmul_sum]
      congr 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum, complete V b hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [e]
    refine sum_mem fun a _ => rk_mem V W _ _ _ (hbm a) _ ?_
    rw [← GlobalTheory.MovedLat.latG_eq]
    exact h a
  · intro h a
    have h1 := colF_mem V W _ _ (hbm a) _ h
    rw [← GlobalTheory.MovedLat.latG_eq] at h1
    have e : (ratW W V Y - realPt V W Y : WO V W) =
        Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] Y i j := by
      ext i j; exact finite_part_apply V W Y i j
    rw [e, colF_pure] at h1
    obtain ⟨f1, f2, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D W y
    exact ((hat_rational_points_and_approx D.host.F D.host.E W.rank _ f1 f2).1 _).1 h1

theorem moved_iff (V W : HSp D) (y : GA D W) (u : WO V W) :
    u ∈ (latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (Bridge.hLat W (FWT.fin W y) : Set (Fin W.rank → D.host.E)) fun _ => True) ↔
      actO V W 1 y⁻¹ u ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (GlobalTheory.Member.latC W : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have h1 : ∀ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
      Matrix.mulVec (finHom V 1).1 z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro z hz
    rw [map_one, Units.val_one, Matrix.one_mulVec]
    exact hz
  constructor
  · exact GlobalTheory.MovedLat.actO_mem V W 1 y⁻¹ _ _ _ _ h1 (GlobalTheory.MovedLat.bwd W y) u
  · intro h
    have h2 := GlobalTheory.MovedLat.actO_mem V W 1 y _ _ _ _ h1 (GlobalTheory.MovedLat.fwd W y) _ h
    have h3 := GlobalTheory.AdelicLatMove.actO_actO_inv V W 1 y u
    rw [inv_one] at h3
    rwa [h3] at h2

theorem cols_mem_iff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E),
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b → ∀ (y : GA D (Wc D i)) (Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E),
      (∀ a, (fun m => ∑ n, Yr m n * b n a) ∈ latG (Wc D i) y) ↔
        actO (Vc D i) (Wc D i) 1 y⁻¹ (ratW (Wc D i) (Vc D i) Yr - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i b hb y Yr
  have hV := (GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hR.βV i)).trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq _).symm
  have hW := (GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hR.βW i)).trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq _).symm
  rw [cols_iff_moved _ _ b hb, moved_iff, ← hV, ← hW]

end GlobalTheory.ColSplit
