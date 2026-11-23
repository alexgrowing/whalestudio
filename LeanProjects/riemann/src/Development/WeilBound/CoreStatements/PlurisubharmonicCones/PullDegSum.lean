import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RootIdxLast
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HtLabelCongr
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.JoinNormal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactDatumIntersectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDatumDegreeSumStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLineStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Last

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) [Fintype (CMType H)]

theorem prod_last {M : Type} [CommMonoid M] (F : CMType H × Fin (D.p + D.q) → M) :
    ∏ r, (if D.p ≤ (r.2 : ℕ) then F r else 1) = ∏ a, F (lastRoot D a) := by
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fin.prod_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [Finset.prod_eq_one (fun i _ => if_neg (by omega)), one_mul]
  simp only [le_add_iff_nonneg_right, zero_le, if_true]
  exact (Fintype.prod_equiv Fin.revPerm (fun a => F (lastRoot D (τ, a))) (fun j => F (τ, Fin.natAdd D.p j))
    (fun a => rfl)).symm

theorem sum_last {M : Type} [AddCommMonoid M] (F : CMType H × Fin (D.p + D.q) → M) :
    ∑ r, (if D.p ≤ (r.2 : ℕ) then F r else 0) = ∑ a, F (lastRoot D a) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [Finset.sum_eq_zero (fun i _ => if_neg (by omega)), zero_add]
  simp only [le_add_iff_nonneg_right, zero_le, if_true]
  exact (Fintype.sum_equiv Fin.revPerm (fun a => F (lastRoot D (τ, a))) (fun j => F (τ, Fin.natAdd D.p j))
    (fun a => rfl)).symm

end Last

theorem pullDeg_sum {K K' I : Type} [Fintype I] {κ : K → K'} (hκ : Function.Injective κ) (a : I → K → ℤ) :
    pullDeg κ (∑ j, a j) = ∑ j, pullDeg κ (a j) := by
  funext x
  simp only [pullDeg, Finset.sum_apply]
  by_cases hx : ∃ y, κ y = x
  · obtain ⟨y, rfl⟩ := hx
    simp only [hκ.extend_apply, Finset.sum_apply]
  · simp only [Function.extend_apply' _ _ _ hx, Pi.zero_apply, Finset.sum_const_zero]

set_option maxHeartbeats 1000000 in
theorem common (h₁ : LevelFree) (h₂ : MuHodge) : Common := by
  intro hG E _ _ _ _ H D Xo l c Y S RM Sys Fx oR II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B hS hdisc hvR hR4 hp hbg hsm hgood hgen
  classical
  subst hS
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := OrLinked.mono_int' c
  have czR : CharZero RM.Ω := charZero_of_injective_ringHom oR.𝔐.cst.injective
  obtain ⟨a1, a2, a3, a4⟩ := GlobalTheory.T.compact_datum_intersection E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  have hfree : ∀ p ∈ S₀ ∪ Dc.SB B, HT.HTFree Or.𝔐 p := fun p hp' => by
    rcases Finset.mem_union.1 hp' with h | h
    · exact hgood.1 p h
    · exact hgood.2 p (Finset.mem_filter.1 h).1
  have hlev : ∀ p ∈ S₀ ∪ Dc.SB B, ∀ q, InFibre Or.𝔐.ξ p q →
      Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ 4) q = Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) q := fun p hp' =>
    h₁ hG.2.2.2.2.2.2.1 E H D l (Xo l) c Y _ Ω K J Dc.y (Or.𝔐.withS _ a1 a2 a3 a4) p hp' (by omega) (hfree p hp')
  let B₄ := levFour Or.𝔐 _ a1 a2 a3 a4 hlev
  have hB₄ : ∀ s, B₄.V s = Or.𝔐.VS (S₀ ∪ Dc.SB B) s := patch_four Or.𝔐 _ hlev

  have eg : genPt oR.𝔐.ξ₀ = genPt Or.𝔐.ξ₀ := by
    have g1 := RegAtDom.map_genPt oR.𝔐.fn_over
    have g2 := RegAtDom.map_genPt (show GlobalTheory.CompanionTheory.Ar.Dominates oR.𝔐.ξ Fx.ξf oR.𝔐.f oR.g from oR.g_over)
    rw [hgen, ← g1, g2]
  obtain ⟨ψ, hψ⟩ := FlagPull.exists_iso oR.𝔐.gen₀ Or.𝔐.gen₀ eg
  have hfin : letI := (Or.𝔐.fn.comp ψ.toRingHom).toAlgebra; Module.Finite oR.𝔐.Ω₀ Ω := by
    have f1 : Or.𝔐.fn.Finite := by
      let _ := Or.𝔐.fn.toAlgebra
      exact Module.finite_of_finrank_pos (Or.cover.2 ▸ Or.cover.1)
    exact RingHom.Finite.comp f1 (RingHom.Finite.of_surjective _ ψ.surjective)
  obtain ⟨Ω₃, _, i₁, i₂, hi, hf₁⟩ := OrLinked.exists_tensor_field oR.𝔐.Ω₀ RM.Ω Ω oR.𝔐.fn _ hfin
  have cz : CharZero Ω₃ := charZero_of_injective_ringHom i₁.injective
  have fd₁ : FiniteDimensional i₁.fieldRange Ω₃ := FiniteDimensional.of_finrank_pos (by
    rw [OrLinked.finrank_fieldRange]
    let _ := i₁.toAlgebra
    exact Module.finrank_pos)
  obtain ⟨K₃, _, ρ, _, κ₁, v₁, κ, v, y, Z, ξ, g₁, g₂, bm₁, bm₂, hy₁, hy₂, I1, I2, har, hbir, hall, htie, hnorm, hd₁, hd₂, hrk⟩ :=
    join_normal i₁ i₂ RM.y Dc.y _ oR.𝔐.ξ Or.𝔐.ξ RM.arith RM.birational fd₁ oR.𝔐.all Or.𝔐.all oR.𝔐.tie Or.𝔐.tie
  obtain ⟨x₁, hx₁'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l (Xo l) c _ _ Y _ RM.Ω RM.K RM.ι RM.y oR.𝔐 hmono
  obtain ⟨x₂, hx₂'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l (Xo l) c _ _ Y _ Ω K J Dc.y Or.𝔐 hmono
  have hx₁ : oR.𝔐.ξ ≫ oR.𝔐.f = (spMap oR.𝔐.fn ≫ x₁) ≫ Y.j := by
    rw [Category.assoc, ← hx₁']; exact oR.𝔐.fn_over
  have hx₂ : Or.𝔐.ξ ≫ Or.𝔐.f = (spMap Or.𝔐.fn ≫ x₂) ≫ Y.j := by
    rw [Category.assoc, ← hx₂']; exact Or.𝔐.fn_over
  have hdisc' : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀ ∪ Dc.SB B := fun p h1 h2 =>
    Finset.mem_union_left _ (hdisc p h1 h2)
  obtain ⟨𝔐, a, j₁, m₁, q1, q2, q3, q4, q5, q6, q7, -, q9⟩ :=
    GlobalTheory.T.hodge_cpt_field_extension E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 _ Z ξ g₁ hx₁ hdisc'
      (fun p hp s => (hvR p hp).2 s) hall htie hnorm hd₁
  have hdom₁ : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ oR.𝔐.ξ (a.hom ≫ g₁) i₁ := by
    show 𝔐.ξ ≫ a.hom ≫ g₁ = _
    rw [← Category.assoc, q1]
    exact hd₁
  have hdom₂ : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ Or.𝔐.ξ (a.hom ≫ g₂) i₂ := by
    show 𝔐.ξ ≫ a.hom ≫ g₂ = _
    rw [← Category.assoc, q1]
    exact hd₂
  have hf𝔐 : 𝔐.f = (a.hom ≫ g₁) ≫ oR.𝔐.f := by rw [q2, Category.assoc]
  obtain ⟨Fl, hbF, -, -, hlF⟩ := FlagPull.flag_pull E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 𝔐
    (a.hom ≫ g₁) j₁ m₁ κ₁ v₁ oR.Fl bm₁ hy₁ hdom₁ hf𝔐 q3 q4 q6 q7 q9 fd₁
  have hZ : g₂ ≫ Or.𝔐.f = g₁ ≫ oR.𝔐.f := by
    refine OrLinked.map_eq_of_generic hnorm hall Y.s Y.proj ?_
    have e1 : ξ ≫ g₁ = spMap i₁ ≫ oR.𝔐.ξ := hd₁
    have e2 : ξ ≫ g₂ = spMap i₂ ≫ Or.𝔐.ξ := hd₂
    have e3 : oR.𝔐.ξ ≫ oR.𝔐.f = spMap oR.𝔐.fn ≫ oR.𝔐.ξ₀ := oR.𝔐.fn_over
    have e4 : Or.𝔐.ξ ≫ Or.𝔐.f = spMap Or.𝔐.fn ≫ Or.𝔐.ξ₀ := Or.𝔐.fn_over
    rw [← Category.assoc, ← Category.assoc, e1, e2, Category.assoc, Category.assoc, e3, e4, ← hψ, ← Category.assoc,
      ← Category.assoc, ← Category.assoc, OrLinked.spMap_spMap', OrLinked.spMap_spMap', OrLinked.spMap_spMap', hi, RingHom.comp_assoc]
  have hvb₄ : ∀ p ∈ S₀ ∪ Dc.SB B, ∀ s, ((Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ 4)).map (Or.𝔐.Vgen s).dualRestrict).IsVBOn
      {q | InFibre Or.𝔐.ξ p q} (labelRk D s) ⊤ := fun p hp' s =>
    vbOn_congr (L := (Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ Or.𝔐.R p)).map (Or.𝔐.Vgen s).dualRestrict) (fun q hq => by
      simp only [Lat.map]
      rw [hlev p hp' q hq]) ((hfree p hp').2 s)
  have hf₄ : (a.hom ≫ g₂) ≫ Or.𝔐.f = 𝔐.f := by rw [q2, Category.assoc, hZ]
  obtain ⟨j, m, hj, hpt, hV⟩ := pull_on (i := i₂) B₄ 𝔐 (a.hom ≫ g₂) _ hx₂ hdisc'
    hvb₄ hdom₂ hf₄ (fun p hp' => by rw [q5]; exact hR4 p hp')
  have hx : 𝔐.ξ ≫ 𝔐.f = (spMap i₁ ≫ spMap oR.𝔐.fn ≫ x₁) ≫ Y.j := by
    have e1 : 𝔐.ξ ≫ a.hom ≫ g₁ = spMap i₁ ≫ oR.𝔐.ξ := hdom₁
    rw [hf𝔐, ← Category.assoc, e1, Category.assoc, hx₁]
    simp only [Category.assoc]
  obtain ⟨β, d, hβ, hβn, hint⟩ := GlobalTheory.T.hodge_cpt_multihomog_form E H D l (Xo l) c _ _ Y _ Ω₃ K₃ ρ y 𝔐 _ hx hmono
  have hdown : ∀ (z : Sp ℂ ⟶ 𝔐.X) (w : (Σ k, ρ k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
      CoordsAt Or.𝔐.ξ Dc.y (z ≫ a.hom ≫ g₂) (fun p => w (v p)) ∧ Or.𝔐.Interior (z ≫ a.hom ≫ g₂) := fun z w hw hz =>
    ⟨HodgePull.coordsAt_pull hdom₂ 𝔐.tie.gen Or.𝔐.tie.cover bm₂ hy₂ (𝔐.all _) (Or.𝔐.all _) hw,
      (abLocus_pullback abLocusOne Or.𝔐.t.semi m.cart.1 _).2 hz⟩
  refine ⟨K₃, inferInstance, ρ, inferInstance, κ₁, v₁, κ, v, Ω₃, inferInstance, cz, y, β, d, bm₁, bm₂, I1, I2, har, hβ, hβn,
    hrk, fun w hw hb hBd => ?_, fun L L' hL hL' => ?_⟩
  · obtain ⟨z, hz, hI⟩ := hint w hw hb
    obtain ⟨c1, c2⟩ := hdown z w hz hI
    exact (Or.bd _ _ c1).1 hBd c2
  obtain ⟨ch₀, hch₀⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  obtain ⟨n, f, cc, -, -, hsum, hloc⟩ := Hd.locally ch₀ hch₀.1
  obtain ⟨l₀⟩ : Nonempty (Fin n) := by
    by_contra h
    have := not_nonempty_iff.1 h
    simp at hsum
  obtain ⟨bb, -, lam, -, hΛ⟩ := hloc l₀
  have hs : ∀ τ k, ∃ z, z ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - z ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    obtain ⟨a, ha, z, hz, h⟩ := Submodule.mem_sup.1
      (Or.i_range τ ▸ LinearMap.mem_range_self (Or.i τ) (bb τ (tailIdx Dc.j_le_N k)))
    exact ⟨z, hz, by rw [← h, add_sub_cancel_right]; exact ha⟩
  choose s hs using hs
  obtain ⟨hsi, hdeg⟩ := GlobalTheory.T.intersection_datum_degree_sum E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B bb s _ hs hΛ
  have hmet := h₂ hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B bb s _ hs hΛ
  have hn : Dc.N - Dc.j = D.q := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · rw [h, Or.N_eq]; omega
    · rw [hbg] at h
      obtain ⟨τ⟩ : Nonempty (CMType H) := (GlobalTheory.T.cm_host_rank_bounds E H).2.1
      exact absurd (congrFun h τ) (by simp)
  simp only [hsm] at hs hdeg hmet
  choose Lp hLp using fun r => ((GlobalTheory.T.block_pullback_herm_line RM.K RM.ι K₃ ρ κ₁ v₁ bm₁).1 (oR.sing r)).exists
  have hroot : Fl.RootLines (fun r => (Lp r).a) fun r => i₁ (oR.e r) := by
    have h := hlF _ _ oR.lines
    have e : (fun r => (Lp r).a) = fun r => pullDeg κ₁ (RM.xdeg r) := funext fun r => by rw [(hLp r).1, oR.sing_deg]
    rwa [e]
  have hiso := core 𝔐 Fl hbir Lp hroot
    (fun r => HodgePull.hodgeLine_pull E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 𝔐 (a.hom ≫ g₁) j₁ m₁ κ₁
      v₁ oR.Fl bm₁ hy₁ hdom₁ hf𝔐 q3 q4 q6 q7 q9 Fl hbF r _ _ _ (oR.hodge r) (hLp r))
    Or.𝔐.t Or.𝔐.tie.gen Or.𝔐.tie.cover Or.𝔐.M (fun τ => Or.𝔐.VS (S₀ ∪ Dc.SB B) (.inr τ)) hdom₂ m j hj hpt
    (fun τ => (hV _).trans (by rw [hB₄]; rfl)) (fun τ => Or.𝔐.Vgen (.inr τ)) (fun τ => a4 (.inr τ)) hn s hsi
    (fun τ k => (hs τ k).1) (muVert Hd B) _ hdeg bm₂ hy₂
    (fun z w hw hz => hmet _ _ (hdown z w hw hz).1 (hdown z w hw hz).2) L L' ?_ (fun w => ?_) hL'
  · obtain ⟨f₁, f₂, hf, hdef⟩ := hiso
    exact ⟨f₁, f₂, hf, fun w hw => hdef w (hint w hw.1 hw.2)⟩
  · rw [hL.1, ← sum_last D fun r => (Lp r).a]
    show pullDeg κ₁ (∑ r, muExp D.p r • (oR.sing r).a) = _
    rw [pullDeg_sum bm₁.1]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold muExp
    split_ifs
    · rw [one_smul, (hLp r).1]
    · rw [zero_smul]
      funext k'
      unfold pullDeg
      by_cases h : ∃ k, κ₁ k = k'
      · obtain ⟨k, rfl⟩ := h
        rw [bm₁.1.extend_apply]
        rfl
      · rw [Function.extend_apply' _ _ _ h]
  · rw [hL.2, ← prod_last D fun r => (Lp r).h w]
    show ∏ r, (oR.sing r).h _ ^ muExp D.p r = _
    refine Finset.prod_congr rfl fun r _ => ?_
    unfold muExp
    split_ifs
    · rw [zpow_one, (hLp r).2]
    · rw [zpow_zero]

end LevelTowerAlt.Comparison₂
