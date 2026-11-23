import Mathlib
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsUnitOfSum
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ComponentDataHeightIdentity
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeSecond
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumLatticeWedgeComapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorWedgeDetChangeStatement

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.TiePrimes

namespace LevelTowerAlt

namespace N1

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem local_frame (Or : CptOrigin Y S₀ Dc Hd) {bb : ∀ τ, Fin Dc.N → W τ}
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} {lam : Ω}
    (hs : ∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ))
    (hΛ : Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)))
    {q : Cpt Or.𝔐.ξ} {ch : ∀ k, J k} (hq : InChart Or.𝔐.ξ (segreCoord Dc.y) ch q) :
    ∃ (s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li)
      (T : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω) (u : Ω),
      (∀ τ, (Or.𝔐.V (Or.sm τ)).IsFrameAt (s' τ) q) ∧ (∀ τ k, s τ k = ∑ k', T τ k' k • s' τ k') ∧
      unitAt Or.𝔐.ξ q u ∧ u * chartMono Dc.y ch Hd.aMu = lam * ∏ τ, (T τ).det := by
  have hT : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  have hreg := fun a ha => (hT.ring ch hq.1 a).1 ha q hq
  obtain ⟨m, f, cc, hf, hcc, hsum, hl⟩ := Hd.locally ch hq.1
  obtain ⟨i, hi⟩ := exists_unit_of_sum (p := q) (fun i => hreg _ (hf i)) (fun i => hreg _ (hcc i)) hsum
  obtain ⟨b, hb, u, ⟨hu0, ⟨n, hn⟩, n', hn'⟩, hΛ'⟩ := hl i
  have hu : unitAt Or.𝔐.ξ q u := ⟨hu0, mem_of_pow_mul hi (hreg _ hn), mem_of_pow_mul hi (hreg _ hn')⟩
  have hsm : ∀ τ k, ∃ x, x ∈ Or.𝔐.Vgen (Or.sm τ) ∧
      Or.i τ (b τ (tailIdx Dc.j_le_N k)) - x ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    have hm : Or.i τ (b τ (tailIdx Dc.j_le_N k)) ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := by
      rw [← Or.i_range τ]
      exact ⟨_, rfl⟩
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 hm
    exact ⟨e, he, by rw [← hae]; simpa using ha⟩
  choose s' hs' using hsm
  have hfr : ∀ τ, (Or.𝔐.V (Or.sm τ)).IsFrameAt (s' τ) q := fun τ => by
    have hrk : labelRk D (Or.bg τ) + labelRk D (Or.sm τ) = Dc.N := by
      rw [Or.rk_bg, Or.rk_sm]
      exact Nat.add_sub_cancel' Dc.j_le_N
    have hsum := GlobalTheory.T.pair_lattice_sum_comap E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 (Or.bg τ) (Or.sm τ) (Or.bg_ne_sm τ τ)
    rw [hrk] at hsum
    have hvb : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsVB Dc.N ⊤ :=
      BlockSumFrame.isVB_comap_of_range _ _ (Or.i τ) (Or.i_inj τ) (Or.i_range τ) hsum
    have h1 := (GlobalTheory.T.segre_chart_bundle Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y (W τ) Dc.N (Dc.W τ) _ hT hvb (Or.lat τ) ch (f i) (b τ)
      hq.1 (hf i) hi.1).1 (hb τ).1 q hq hi
    exact (GlobalTheory.T.is_frame_at_tail_of_is_frame_at_comap_sup_lattice Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (W τ) (Or.i τ) (Or.𝔐.V (Or.bg τ)) (Or.𝔐.V (Or.sm τ))
      (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) Dc.N Dc.j Dc.j_le_N (b τ) (s' τ) q (Or.i_inj τ)
      (Or.i_range τ) (MuIndep.blocks_disjoint Or τ) (fun _ hx => MuIndep.stalk_le_gen _ _ _ hx)
      (fun _ hx => MuIndep.stalk_le_gen _ _ _ hx) h1 (by rw [(hb τ).2.2, Or.F_eq τ]) (hs' τ)).1
  have hq' := fun τ => MuIndep.quot_basis Dc.j_le_N (b := b τ) (F := Hd.F τ) (hb τ).1.2.2.2.1 (hb τ).2.1 (hb τ).2.2
  have hco : ∀ τ k, ∃ t : Fin (Dc.N - Dc.j) → Ω, ∑ a, t a • (Hd.F τ).mkQ (b τ (tailIdx Dc.j_le_N a)) =
      (Hd.F τ).mkQ (bb τ (tailIdx Dc.j_le_N k)) := fun τ k =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (by rw [(hq' τ).2]; trivial)
  choose t ht using hco
  refine ⟨s', fun τ => Matrix.of fun a k => t τ k a, u, hfr, fun τ k => ?_, hu, ?_⟩
  · have h1 : bb τ (tailIdx Dc.j_le_N k) - ∑ a, t τ k a • b τ (tailIdx Dc.j_le_N a) ∈ Hd.F τ := by
      refine (Submodule.Quotient.eq (Hd.F τ)).1 ?_
      have := ht τ k
      simp_rw [← map_smul] at this
      rw [← map_sum] at this
      exact this.symm
    rw [Or.F_eq τ, Submodule.mem_comap, map_sub, map_sum] at h1
    rw [← sub_eq_zero]
    refine (Submodule.disjoint_def.1 (MuIndep.blocks_disjoint Or τ)) _ ?_
      (sub_mem (hs τ k).1 (sum_mem fun a _ => Submodule.smul_mem _ _ (hs' τ a).1))
    have e : s τ k - ∑ a, t τ k a • s' τ a =
        (Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - ∑ a, Or.i τ (t τ k a • b τ (tailIdx Dc.j_le_N a))) -
          (Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k) +
          ∑ a, t τ k a • (Or.i τ (b τ (tailIdx Dc.j_le_N a)) - s' τ a) := by
      simp only [map_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    show s τ k - ∑ a, t τ k a • s' τ a ∈ _
    rw [e]
    exact add_mem (sub_mem h1 (hs τ k).2) (sum_mem fun a _ => Submodule.smul_mem _ _ (hs' τ a).2)
  · exact GlobalTheory.T.tensor_wedge_det_change (CMType H) Ω (fun τ => W τ ⧸ Hd.F τ) (Dc.N - Dc.j)
      (fun τ a => (Hd.F τ).mkQ (b τ (tailIdx Dc.j_le_N a)))
      (fun τ a => (Hd.F τ).mkQ (bb τ (tailIdx Dc.j_le_N a))) (fun τ => Matrix.of fun a k => t τ k a) _ _
      (fun τ => (hq' τ).1) (fun τ => (hq' τ).2) (fun τ k => (ht τ k).symm) (hΛ'.symm.trans hΛ)

theorem local_change (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (hpr : ∀ p ∈ S₀ ∪ Dc.SB B, p.Prime)
    (hvb : ∀ s, (Or.𝔐.VS (S₀ ∪ Dc.SB B) s).IsVB (labelRk D s) (Or.𝔐.Vgen s))
    {q : Cpt Or.𝔐.ξ} {ch : ∀ k, J k} (hq : InChart Or.𝔐.ξ (segreCoord Dc.y) ch q)
    {s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs' : ∀ τ, (Or.𝔐.V (Or.sm τ)).IsFrameAt (s' τ) q) :
    ∃ (b : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li)
      (A : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω),
      (∀ τ, (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)).IsFrameAt (b τ) q) ∧ (∀ τ k, b τ k = ∑ k', A τ k' k • s' τ k') ∧
      unitAt Or.𝔐.ξ q ((∏ τ, (A τ).det) / ∏ p ∈ Dc.SB B,
        (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y ch (-Dc.vdeg p))) := by
  have hS : ∀ p ∈ Dc.SB B, p ∈ Dc.S := fun p hp => (Finset.mem_filter.1 hp).1
  have P := fun s => GlobalTheory.T.lattice_patch_at_primes Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (S₀ ∪ Dc.SB B) (Or.𝔐.dR s) (fun p => Or.𝔐.HT p s) q hpr
  have P₀ := fun s => GlobalTheory.T.lattice_patch_at_primes Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li S₀ (Or.𝔐.dR s) (fun p => Or.𝔐.HT p s) q Or.𝔐.S_prime
  have hoff : ∀ p ∈ Dc.SB B, ¬ InFibre Or.𝔐.ξ p q → unitAt Or.𝔐.ξ q
      (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y ch (-Dc.vdeg p)) :=
    fun p hp h => unit_off_fibre hq (Dc.vertical p (hS p hp)) h
  by_cases h : ∃ p ∈ Dc.SB B, InFibre Or.𝔐.ξ p q
  · obtain ⟨p, hp, hf⟩ := h
    have hb : ∀ τ, ∃ (b : Fin (Dc.N - Dc.j) → Or.𝔐.Li) (A : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω),
        (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)).IsFrameAt b q ∧ ∀ k, b k = ∑ k', A k' k • s' τ k' := fun τ => by
      have h1 := hvb (Or.sm τ)
      rw [Or.rk_sm τ] at h1
      obtain ⟨U, hU, b, hsp, hfr⟩ := h1 q trivial
      have h2 : ∀ k, ∃ t : Fin (Dc.N - Dc.j) → Ω, ∑ a, t a • s' τ a = b k := fun k =>
        (Submodule.mem_span_range_iff_exists_fun Ω).1 (le_span_frame (L := Or.𝔐.V (Or.sm τ))
          (U := Or.𝔐.Vgen (Or.sm τ)) (Or.𝔐.vb (Or.sm τ)) (hs' τ) (hsp ▸ Submodule.subset_span ⟨k, rfl⟩))
      choose t ht using h2
      exact ⟨b, Matrix.of fun a k => t k a, hfr q trivial hU, fun k => (ht k).symm⟩
    choose b A hb hA using hb
    refine ⟨b, A, hb, hA, ?_⟩
    have hHT : ∀ τ, (Or.𝔐.HT p (Or.sm τ)).IsFrameAt (b τ) q := fun τ =>
      ⟨(hb τ).1, ((P (Or.sm τ)).2 p (Finset.mem_union_right _ hp) hf).symm.trans (hb τ).2⟩
    have hv := Or.vert p (hS p hp) q hf ch hq (fun τ => s' τ ∘ Fin.cast (Or.rk_sm τ))
      (fun τ => b τ ∘ Fin.cast (Or.rk_sm τ)) (fun τ => (A τ).submatrix (Fin.cast (Or.rk_sm τ)) (Fin.cast (Or.rk_sm τ)))
      (fun τ => cast_frame _ (hs' τ)) (fun τ => cast_frame _ (hHT τ)) (fun τ k => cast_sum _ (hA τ) k)
    simp only [cast_det] at hv
    have hrest := unitAt_prod ((Dc.SB B).erase p) _ fun p' hp' => hoff p' (Finset.mem_of_mem_erase hp')
      (not_inFibre_two (Dc.S_prime p (hS p hp)) (Dc.S_prime p' (hS p' (Finset.mem_of_mem_erase hp')))
        (Finset.ne_of_mem_erase hp').symm hf)
    rw [← Finset.mul_prod_erase _ _ hp, ← div_div, div_eq_mul_inv (_ / _)]
    exact unitAt_mul hv (unitAt_inv hrest)
  · push Not at h
    refine ⟨s', fun _ => 1, fun τ => ⟨(hs' τ).1, Eq.trans ?_ (hs' τ).2⟩, fun τ k => by simp [Matrix.one_apply], ?_⟩
    · by_cases h' : ∃ p ∈ S₀, InFibre Or.𝔐.ξ p q
      · obtain ⟨p, hp, hq⟩ := h'
        exact ((P _).2 p (Finset.mem_union_left _ hp) hq).trans ((P₀ _).2 p hp hq).symm
      · push Not at h'
        exact ((P _).1 fun p hp => (Finset.mem_union.1 hp).elim (h' p) (h p)).trans ((P₀ _).1 h').symm
    · simp only [Matrix.det_one, Finset.prod_const_one, one_div]
      exact unitAt_inv (unitAt_prod _ _ fun p hp => hoff p hp (h p hp))

end Main

end N1

open N1

theorem det_lattice_tensor_isDegOn_muTwDeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (bb : ∀ τ, Fin Dc.N → W τ) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (lam : Ω), (∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ)) → Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)) → (∀ τ, LinearIndependent Ω (s τ)) ∧ (Lat.tens (fun τ => detLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ Dc.y (muTwDeg Hd B) (lam⁻¹ * ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p)) := by
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B bb s lam hs hΛ
  obtain ⟨hpr, -, -, hvb⟩ := component_data_height_identity E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  have hS : ∀ p ∈ Dc.SB B, p ∈ Dc.S := fun p hp => (Finset.mem_filter.1 hp).1
  have hnd : ∀ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vnum p) ≠ 0 ∧ MvPolynomial.aeval Dc.y (Dc.vden p) ≠ 0 := by
    intro p hp
    have hv := Dc.vertical p (hS p hp)
    obtain ⟨bf, bg, hf, hg, -⟩ := hv.degrees
    exact ⟨fun h => hv.num_not_mem ((mem_coord_iff _ hf).2 h), fun h => hv.den_not_mem ((mem_coord_iff _ hg).2 h)⟩
  have hP : ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => div_ne_zero (hnd p hp).2 (hnd p hp).1
  obtain ⟨c₀, hc₀⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  obtain ⟨s₀, T₀, u₀, hf₀, hT₀, hu₀, e₀⟩ := local_frame Or hs hΛ hc₀
  have n₀ : lam * ∏ τ, (T₀ τ).det ≠ 0 := e₀ ▸ mul_ne_zero hu₀.1 (chartMono_ne (ne_of_seg hc₀.1) _)
  have hlam : lam ≠ 0 := left_ne_zero_of_mul n₀
  have hli : ∀ τ, LinearIndependent Ω (s τ) := fun τ => li_of_det (hf₀ τ).1 (hT₀ τ)
    (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul n₀) τ (Finset.mem_univ τ))
  refine ⟨hli, mul_ne_zero (inv_ne_zero hlam) hP, fun q _ ch hq => ?_⟩
  have hc := ne_of_seg hq.1
  obtain ⟨s', T, u, hf, hT, hu, e⟩ := local_frame Or hs hΛ hq
  have n₁ : ∏ τ, (T τ).det ≠ 0 := right_ne_zero_of_mul (e ▸ mul_ne_zero hu.1 (chartMono_ne hc _))
  have hd : ∀ τ, (T τ).det ≠ 0 := fun τ => Finset.prod_ne_zero_iff.1 n₁ τ (Finset.mem_univ τ)
  obtain ⟨b, A, hb, hA, hun⟩ := local_change Or B hpr hvb hq hf
  have hg : ∀ τ, (detLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) (s τ)).IsGenAt q ((T τ)⁻¹ * A τ).det := fun τ =>
    determinant_lattice_generator _ _ _ _ _ _ _ _ _ _ (hli τ) (hb τ) (mat_comp (mat_inv (hT τ) (hd τ)) (hA τ))
  rw [(tens_gen (fun _ => -1) hg).2]
  have n₂ := chartMono_ne hc (muTwDeg Hd B)
  refine span_eq_of_unit (mul_ne_zero n₂ (mul_ne_zero (inv_ne_zero hlam) hP)) ?_
  have e1 : ∏ τ, ((T τ)⁻¹ * A τ).det ^ (-1 : ℤ) = (∏ τ, (T τ).det) / ∏ τ, (A τ).det := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', _root_.zpow_neg_one, mul_inv, inv_inv,
      div_eq_mul_inv]
  have e2 : ∏ p ∈ Dc.SB B, (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
      chartMono Dc.y ch (-Dc.vdeg p)) =
      (∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p))⁻¹ *
        (chartMono Dc.y ch (∑ p ∈ Dc.SB B, Dc.vdeg p))⁻¹ := by
    rw [chartMono_sum hc, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => by rw [inv_div, chartMono_neg]
  have n₃ := chartMono_ne hc Hd.aMu
  have n₄ := chartMono_ne hc (∑ p ∈ Dc.SB B, Dc.vdeg p)
  have n₅ : ∏ τ, (A τ).det ≠ 0 := fun h0 => hun.1 (by rw [h0, zero_div])
  rw [e2] at hun
  have e3 : ∏ τ, (T τ).det = u * chartMono Dc.y ch Hd.aMu / lam := by rw [e]; field_simp
  convert unitAt_mul hu (unitAt_inv hun) using 1
  show _ / (chartMono Dc.y ch (Hd.aMu + ∑ p ∈ Dc.SB B, Dc.vdeg p) * _) = _
  rw [e1, e3, chartMono_add hc]
  field_simp

end LevelTowerAlt
