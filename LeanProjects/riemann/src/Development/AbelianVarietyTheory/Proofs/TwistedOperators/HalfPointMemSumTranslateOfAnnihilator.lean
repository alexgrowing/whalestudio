import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOSmulHalf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DivisiblePontryaginAnnihilatorDuality
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHalfEqDoubleAnnihilator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteQuotientAnnihilatorStandardLatticeConjHalf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteRepsHalfStandardHomModNsmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

namespace GlobalTheory.AnnSum

theorem latO_comm {D : D7} (S T : HSp D) {A A' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {B B' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hA : A.FG) (hB : B.FG)
    (hA' : Submodule.IsLattice D.host.E A') (hB' : Submodule.IsLattice D.host.E B') : ∃ N : ℕ, 0 < N ∧
    ∀ y ∈ latO S T (A : Set (Fin S.rank → D.host.E)) (B : Set (Fin T.rank → D.host.E)) (fun _ => True),
      N • y ∈ latO S T (A' : Set (Fin S.rank → D.host.E)) (B' : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hA hB
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hA' hB'
  refine ⟨K * M, Nat.mul_pos hK hM, fun y hy => ?_⟩
  rw [mul_smul]
  refine hKm _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, GlobalTheory.LatVac.infPart_of_mem hy i j,
      mul_zero, Matrix.zero_apply]
  · rw [Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact hden y hy i j

theorem stdHom_eq {D : D7} (S T : HSp D) : GlobalTheory.AdForm.stdHom S T =
    latO S T (Formalism.L2.Col.stdLat D.host.E S.rank : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
      (Formalism.L2.Col.stdLat D.host.E T.rank : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (fun _ => True) := by
  rw [GlobalTheory.AdForm.coe_colStdLat, GlobalTheory.AdForm.coe_colStdLat]

theorem std_le_hat {D : D7} (S T : HSp D) {A : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {B : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hA : IsSelfDualC S A) (hB : IsSelfDualC T B)
    {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ GlobalTheory.AdForm.stdHom S T,
      N • u ∈ GlobalTheory.ChiGrid.hatMx (𝔪 • GlobalTheory.ChiGrid.homLat A B) := by
  obtain ⟨M, hM, h1⟩ := latO_comm S T (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)).fg
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank)).fg hA.1 hB.1
  obtain ⟨K, hK, h2⟩ := GlobalTheory.GridWeil.exists_nsmul_latO (T := T) (ΛT := B) hA h𝔪
  refine ⟨K * M, Nat.mul_pos hK hM, fun u hu => ?_⟩
  rw [mul_smul]
  rw [stdHom_eq] at hu
  exact h2 _ (h1 u hu)

theorem hat_le_std {D : D7} (S T : HSp D) {A : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {B : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hA : IsSelfDualC S A) (hB : IsSelfDualC T B)
    (𝔪 : Ideal (𝓞 D.host.E)) : ∃ N : ℕ, 0 < N ∧ ∀ v ∈ GlobalTheory.ChiGrid.hatMx (𝔪 • GlobalTheory.ChiGrid.homLat A B),
      N • v ∈ GlobalTheory.AdForm.stdHom S T := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.GridWeil.exists_nsmul_hatMx (S := S) (T := T)
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)) (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank))
    (GlobalTheory.ChiGrid.homLat A B) (Module.Finite.iff_fg.1 (homLat_fg hA.1 hB.1.fg))
  refine ⟨K, hK, fun v hv => ?_⟩
  rw [stdHom_eq]
  refine h _ (AddSubgroup.closure_mono ?_ hv)
  rintro _ ⟨α, hα, x, hx, rfl⟩
  exact ⟨α, hα, x, Submodule.smul_le_right hx, rfl⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem act_le_std (D : D7) (S T : HSp D) (g : GA D T) : ∃ N : ℕ, 0 < N ∧
    ∀ u ∈ GlobalTheory.AdForm.stdHom S T, N • actO S T 1 g u ∈ GlobalTheory.AdForm.stdHom S T := by
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T)
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)).fg
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank)).fg
  rw [← stdHom_eq] at hden
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.AdForm.exists_nsmul_mem_stdHom S T
  obtain ⟨N, hN, h'⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (Formalism.L2.Herm.intAf D.host.F D.host.E)
    GlobalTheory.PlaceDatum.exists_den_adele ((mt T g).map (toEAf D))
  refine ⟨K * (N * M), Nat.mul_pos hK (Nat.mul_pos hN hM), fun u hu => ?_⟩
  have hact : ∀ i j, actO S T 1 g u i j = ∑ k, mt T g i k * u k j := fun i j => by
    have h1 : mt S (1 : GA D S)⁻¹ = 1 := by rw [inv_one]; rfl
    unfold actO
    rw [h1, Matrix.mul_one, Matrix.mul_apply]
  rw [mul_smul]
  refine hKm _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, hact, map_sum, Finset.sum_eq_zero,
      mul_zero, Matrix.zero_apply]
    intro k _
    rw [RingHom.map_mul, GlobalTheory.LatVac.infPart_of_mem hu k j, mul_zero]
  · rw [Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, map_natCast, hact, map_sum, Finset.mul_sum]
    refine sum_mem fun k _ => ?_
    have h3 := mul_mem (h' i k) (hden u hu k j)
    rw [Matrix.map_apply, mul_mul_mul_comm, ← Nat.cast_mul, ← RingHom.map_mul] at h3
    exact h3

end GlobalTheory.AnnSum

namespace GlobalTheory.AnnSum

variable {D : D7}

def halfSub {m n : ℕ} (f : AE D) : AddSubgroup (Mx D m n) where
  carrier := {u | IsHalf f u}
  zero_mem' := fun i j => by simp
  add_mem' := fun {u v} hu hv i j => by rw [Matrix.add_apply, mul_add, hu i j, hv i j]
  neg_mem' := fun {u} hu i j => by rw [Matrix.neg_apply, mul_neg, hu i j]

theorem exists_div_half {m n : ℕ} (f : AE D) (k : ℕ) (hk : 0 < k) (x : Mx D m n) (hx : IsHalf f x) :
    ∃ x' : Mx D m n, IsHalf f x' ∧ k • x' = x := by
  refine ⟨algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹) • x, fun i j => ?_, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx i j]
  · ext i j
    have hF : (k : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, ← mul_assoc,
      show ((k : AE D)) = algebraMap D.host.F (AE D) (k : D.host.F) from (map_natCast _ k).symm,
      ← map_mul, mul_inv_cancel₀ hF, map_one, one_mul]

end GlobalTheory.AnnSum

namespace GlobalTheory.AnnSum

variable {D : D7}

theorem nsmul_smul_comm' {m n : ℕ} (k : ℕ) (c : AE D) (v : Mx D m n) : k • (c • v) = c • (k • v) := by
  ext a b
  simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ann_sum_gen (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : IsIdemSum e Q) (g : GA D T) (Mh : AddSubgroup (WO S T))
    (NA NB NC : ℕ) (hNA : 0 < NA) (hNB : 0 < NB) (hNC : 0 < NC)
    (hA : ∀ u ∈ GlobalTheory.AdForm.stdHom S T, IsHalf e u → NA • u ∈ Mh)
    (hB : ∀ v ∈ Mh, NB • v ∈ GlobalTheory.AdForm.stdHom S T)
    (hC : ∀ u ∈ GlobalTheory.AdForm.stdHom S T, NC • actO S T 1 g u ∈ GlobalTheory.AdForm.stdHom S T)
    (Z : WO S T) (hZ : IsHalf e Z)
    (hyp : ∀ y : WO S T, IsHalf (cA D e) y → (∀ v ∈ Mh, ψ (symplO S T (e • v) y) = 1) →
      (∀ v ∈ Mh, ψ (symplO S T (actO S T 1 g (e • v)) y) = 1) → ψ (symplO S T Z y) = 1) :
    ∃ a ∈ Mh, ∃ b ∈ Mh, Z = e • a + actO S T 1 g (e • b) := by
  classical
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hχ := GlobalTheory.PlaceModel.isBichar_symplO S T ψ
  let f1 : WO S T →+ WO S T := AddMonoidHom.mk' (fun v => e • v) (fun a b => smul_add e a b)
  let f2 : WO S T →+ WO S T := AddMonoidHom.mk' (fun v => actO S T 1 g (e • v))
    (fun a b => by rw [smul_add, GlobalTheory.CosDual.actO_add])
  let Lsum : AddSubgroup (WO S T) := Mh.map f1 ⊔ Mh.map f2
  have he_half : ∀ v : WO S T, IsHalf e (e • v) := fun v a b => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  have heint : ∀ u ∈ GlobalTheory.AdForm.stdHom S T, e • u ∈ GlobalTheory.AdForm.stdHom S T := fun u hu =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])) _ hu
  have hN : 0 < NA * (NB * NC) := Nat.mul_pos hNA (Nat.mul_pos hNB hNC)
  have hNL : ∀ u ∈ GlobalTheory.AnnConjHalf.stdHalf S T e, (NA * (NB * NC)) • u ∈ Lsum := by
    intro u hu
    have h1 : NA • u ∈ Lsum := by
      refine AddSubgroup.mem_sup_left ⟨NA • u, hA u hu.1 hu.2, ?_⟩
      change e • (NA • u) = NA • u
      rw [← nsmul_smul_comm']
      congr 1
      exact Matrix.ext fun a b => hu.2 a b
    rw [mul_nsmul]
    exact AddSubgroup.nsmul_mem _ h1 _
  have hLN : ∀ u ∈ Lsum, (NA * (NB * NC)) • u ∈ GlobalTheory.AnnConjHalf.stdHalf S T e := by
    intro u hu
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hu
    obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hy
    obtain ⟨b, hb, rfl⟩ := AddSubgroup.mem_map.1 hz
    refine ⟨?_, ?_⟩
    · rw [smul_add]
      refine add_mem ?_ ?_
      · have h1 : NB • (e • a) ∈ GlobalTheory.AdForm.stdHom S T := by
          rw [nsmul_smul_comm']; exact heint _ (hB a ha)
        have e1 : (NA * (NB * NC)) • f1 a = (NA * NC) • (NB • (e • a)) := by
          rw [← mul_nsmul']; congr 1; ring
        rw [e1]
        exact AddSubgroup.nsmul_mem _ h1 _
      · have h1 : NC • f2 (NB • b) ∈ GlobalTheory.AdForm.stdHom S T := hC _ (heint _ (hB b hb))
        rw [map_nsmul, ← mul_nsmul'] at h1
        have e1 : (NA * (NB * NC)) • f2 b = NA • ((NC * NB) • f2 b) := by
          rw [← mul_nsmul']; congr 1; ring
        rw [e1]
        exact AddSubgroup.nsmul_mem _ h1 _
    · refine GlobalTheory.AnnConjHalf.half_nsmul ?_ _
      intro a' b'
      rw [Matrix.add_apply, mul_add]
      congr 1
      · exact he_half a a' b'
      · exact GlobalTheory.CosDual.half_actO S T e g (e • b) (he_half b) a' b'
  have h2 : ∀ x ∈ halfSub (m := T.rank) (n := S.rank) e, (∀ y ∈ GlobalTheory.AnnConjHalf.annHalf ψ S T e,
      ψ (symplO S T x y) = 1) → x ∈ GlobalTheory.AnnConjHalf.stdHalf S T e := fun x hx H =>
    ⟨GlobalTheory.HalfDoubleAnn.mem_of_ann_ann D ψ hψ S T Q e he x hx (fun y hy hann => H y ⟨hy, hann⟩), hx⟩
  have hann : ∀ y ∈ halfSub (m := T.rank) (n := S.rank) (cA D e), (∀ u ∈ Lsum, ψ (symplO S T u y) = 1) →
      ψ (symplO S T Z y) = 1 := fun y hy h =>
    hyp y hy (fun v hv => h _ (AddSubgroup.mem_sup_left ⟨v, hv, rfl⟩))
      (fun v hv => h _ (AddSubgroup.mem_sup_right ⟨v, hv, rfl⟩))
  have hNx : (NA * (NB * NC)) • Z ∈ GlobalTheory.AnnConjHalf.stdHalf S T e := by
    refine h2 _ (GlobalTheory.AnnConjHalf.half_nsmul hZ _) fun y hy => ?_
    rw [hχ.nsmul]
    refine hann _ (GlobalTheory.AnnConjHalf.half_nsmul hy.1 _) fun u hu => ?_
    rw [← hχ.nsmul]
    have h := hLN u hu
    exact hy.2 _ h.1 h.2
  have key : Z ∈ Lsum := GlobalTheory.DualTransfer.mem_of_double_annihilator (fun x y => ψ (symplO S T x y)) hχ
    (halfSub e) (halfSub (cA D e)) (GlobalTheory.AnnConjHalf.stdHalf S T e) (GlobalTheory.AnnConjHalf.annHalf ψ S T e) Lsum
    (fun u hu => hu.2) (fun u hu => hu.1)
    (sup_le (by rintro _ ⟨v, -, rfl⟩; exact he_half v)
      (by rintro _ ⟨v, -, rfl⟩; exact GlobalTheory.CosDual.half_actO S T e g (e • v) (he_half v)))
    (fun u hu y hy => hy.2 u hu.1 hu.2) h2
    (fun y hy H => ⟨hy, fun x hx hxh => H x ⟨hx, hxh⟩⟩)
    (fun k hk x hx => exists_div_half e k hk x hx)
    (fun k hk y hy => exists_div_half (cA D e) k hk y hy)
    (fun k hk a b hab => by
      have h0 : k • (a - b) = 0 := by rw [smul_sub]; exact sub_eq_zero.2 hab
      exact sub_eq_zero.1 (GlobalTheory.AnnConjHalf.nsmul_eq_zero_WO S T hk _ h0))
    (fun k hk => by
      obtain ⟨R, hR⟩ := GlobalTheory.HalfStdFin.exists_reps_half_stdHom D S T Q e he k hk
      refine ⟨(R : Set (WO S T)), R.finite_toSet, fun t ht => ?_⟩
      obtain ⟨r, hr, v, hv, hvh, htv⟩ := hR t ht.1 ht.2
      exact ⟨r, hr, v, ⟨hv, hvh⟩, htv⟩)
    (fun k hk => by
      obtain ⟨R, hR⟩ := GlobalTheory.AnnConjHalf.ann_conj_half_finite D ψ hψ S T Q e he k hk
      refine ⟨(R : Set (WO S T)), R.finite_toSet, fun t ht => ?_⟩
      obtain ⟨r, hr, v, hvh, hv, htv⟩ := hR t ht.1 ht.2
      exact ⟨r, hr, v, ⟨hvh, hv⟩, htv⟩)
    _ hN hNL hLN Z hZ hNx hann
  obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.1 key
  obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hy
  obtain ⟨b, hb, rfl⟩ := AddSubgroup.mem_map.1 hz
  exact ⟨a, ha, b, hb, hyz.symm⟩

end GlobalTheory.AnnSum

namespace GlobalTheory.AnnSum

theorem ann_sum : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ Z : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf e Z →
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO _ _ 1 g (e • v)) y) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) = 1) →
    ∃ a ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∃ b ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), Z = e • a + actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • b) := by
  intro D hq T L μ0 hL sc G W M hM i hi e he g Z hZ hyp
  have dS : IsSelfDualC (G.pS (.core i)) (G.latS (.core i)) := isSelfDualC_neg (G.sp.P_is (i + 1) hi).sd
  have dT : IsSelfDualC (G.pT (.core i)) (G.latT (.core i)) := (G.sp.P_is i hi.le).sd
  obtain ⟨NA, hNA, hA⟩ := std_le_hat _ _ dS dT (G.pl.modul_ne_bot sc)
  obtain ⟨NB, hNB, hB⟩ := hat_le_std _ _ dS dT G.modul
  obtain ⟨NC, hNC, hC⟩ := act_le_std D (G.pS (.core i)) (G.pT (.core i)) g
  exact ann_sum_gen W.ψ W.ψ_std _ _ G.pl.W0 e he g _ NA NB NC hNA hNB hNC (fun u hu _ => hA u hu) hB hC Z hZ hyp

end GlobalTheory.AnnSum
