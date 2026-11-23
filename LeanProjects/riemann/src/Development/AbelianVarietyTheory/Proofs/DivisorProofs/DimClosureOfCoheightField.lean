import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImage
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VdmRec.CutSec

section General

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt GlobalTheory.Cartier

theorem exists_finite_specializes {T : Type*} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T] {C : Set T}
    (hC : IsClosed C) : ∃ G : Set T, G.Finite ∧ G ⊆ C ∧ ∀ x ∈ C, ∃ g ∈ G, g ⤳ x := by
  obtain ⟨S, hS, hcl, hirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  choose g hg using fun t : S => QuasiSober.sober (hirr t t.2) (hcl t t.2)
  have := hS.to_subtype
  refine ⟨Set.range g, Set.finite_range g, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨t, t.2, (hg t).mem⟩
  · rintro x ⟨t, ht, hx⟩
    exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, (hg ⟨t, ht⟩).specializes hx⟩

theorem dim_closure_of_coheight_field {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (t : X ⟶ Spec (.of K))
    [LocallyOfFiniteType t] {n : ℕ} (hX : topologicalKrullDim X = (n + 1 : ℕ)) {w : X} (hw : Order.coheight w = 1) :
    topologicalKrullDim (closure ({w} : Set X)) = n := by
  have hgen : genericPoint X ∉ closure ({w} : Set X) := by
    intro h
    have e : w = genericPoint X :=
      ((genericPoint_specializes w).antisymm (specializes_iff_mem_closure.2 h)).eq.symm
    rw [e, Order.coheight_eq_zero.2 (fun y _ => genericPoint_specializes y)] at hw
    exact zero_ne_one hw
  have hX1 : topologicalKrullDim (Set.univ : Set X) = (n + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hX
  have hup : topologicalKrullDim (closure ({w} : Set X)) + 1 ≤ (n + 1 : ℕ) :=
    hX1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ
      fun x _ => ⟨genericPoint X, trivial, hgen, genericPoint_specializes x⟩
  refine le_antisymm (GlobalTheory.PullVanish.withBot_le_of_add_one_le hup) ?_
  obtain ⟨A, _, _, _, _, _, j, _, ⟨a, ha⟩, -, hA⟩ := exists_affine_chart_trdeg_eq t w
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast K (A := A)
  have hdimX : topologicalKrullDim X ≤ (d : ℕ) := by
    refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨B, _, _, _, _, _, j', _, ⟨b, rfl⟩, -, hB⟩ := exists_affine_chart_trdeg_eq t x
    refine ⟨Set.range j', j'.isOpenEmbedding.isOpen_range, ⟨b, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding j'.isOpenEmbedding.isEmbedding rfl]
    exact ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).trans
      (ringKrullDim_eq_of_trdeg_eq K B (hB.trans (hA.symm.trans hd)))).le
  have hh : a.asIdeal.height = 1 := by
    rw [← hw, ← ha, coheight_apply_of_isOpenImmersion]
    exact idealHeight_eq_coheight (CommRingCat.of A) a
  have : a.asIdeal.IsPrime := a.isPrime
  have hF := height_add_ringKrullDim_quotient_of_finiteType K a.asIdeal
  rw [hh, ringKrullDim_eq_of_trdeg_eq K A hd] at hF
  have hlow : topologicalKrullDim (Set.range j ∩ closure {j a} : Set X) ≤
      topologicalKrullDim (closure ({w} : Set X)) := by
    rw [ha]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j a] at hlow
  refine le_trans ?_ hlow
  rw [hX, ← hF] at hdimX
  generalize ringKrullDim (A ⧸ a.asIdeal) = u at hdimX
  induction u using WithBot.recBotCoe with
  | bot => simp at hdimX
  | coe u =>
    induction u using ENat.recTopCoe with
    | top => exact_mod_cast le_top
    | coe u =>
      have : n + 1 ≤ 1 + u := by exact_mod_cast hdimX
      exact_mod_cast (by omega : n ≤ u)

theorem dim_closure_of_coheight {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] {n : ℕ} (hZ : topologicalKrullDim Z = (n + 1 : ℕ)) {w : Z}
    (hw : Order.coheight w = 1) : topologicalKrullDim (closure ({w} : Set Z)) = n := by
  obtain ⟨l, hl⟩ := CharP.exists Γ(Z, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Z, ⊤) l with hp | rfl
  · have : Fact l.Prime := ⟨hp⟩
    let := ZMod.algebra Γ(Z, ⊤) l
    obtain ⟨N, jN, _, hjN⟩ := hX.isProjOver
    have := isProper_str k N
    have : IsProper p := hjN ▸ inferInstance
    have : IsFinite (spMap (Int.castRingHom k)) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
    have e : strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : LocallyOfFiniteType (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))) := e ▸ inferInstance
    have : LocallyOfFiniteType (strHom (ZMod l) Z) := locallyOfFiniteType_of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact dim_closure_of_coheight_field (strHom (ZMod l) Z) hZ hw
  · have := CharP.charP_to_charZero Γ(Z, ⊤)
    have h := GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one k Z (i ≫ p) n (hX.of_isClosedImmersion i this hZ) _
      (redι (clo w)) (by rw [GlobalTheory.PullVanish.redι_genericPoint]; exact hw)
    exact (topologicalKrullDim_eq_of_isEmbedding (redι (clo w)).isClosedEmbedding.isEmbedding
      (range_redι _)).trans h

theorem charZero_of_specializes {X : Scheme.{0}} {z w : X} (h : z ⤳ w) (hw : CharZero (X.residueField w)) :
    CharZero (X.residueField z) := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  have h₁ : IsUnit (n : X.presheaf.stalk w) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
    exact (Nat.cast_ne_zero (R := X.residueField w)).2 h0
  have h₂ := (h₁.map (X.presheaf.stalkSpecializes h).hom).map (X.residue z).hom
  rw [map_natCast, map_natCast, hn] at h₂
  exact not_isUnit_zero h₂

theorem exists_of_cutMult_ne_zero {X : Scheme.{0}} [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB) (s : L.Sec) {z w : X}
    (h : cutMult hL s z w ≠ 0) :
    ∃ w', redι (clo z) w' = w ∧ Order.coheight w' = 1 ∧ w ∉ Out.nonzeroLocus s := by
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (redι (clo z))
  unfold cutMult at h
  split_ifs at h with hg
  · by_cases hw : ∃ w', redι (clo z) w' = w
    · obtain ⟨w', rfl⟩ := hw
      rw [(redι (clo z)).isClosedEmbedding.injective.extend_apply] at h
      refine ⟨w', rfl, CartierDiv.coheight_eq_one_of_mult_ne_zero h, fun hs => ?_⟩
      refine notMem_supp_divOfSec.2 ?_ (CartierDiv.mem_supp_of_mult_ne_zero h)
      rw [GlobalTheory.ZV.GraphSystem.nonzeroLocus_pull]
      exact hs
    · rw [Function.extend_apply' _ _ _ hw] at h
      exact absurd rfl h
  · exact absurd rfl h

end General

section Cut

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt GlobalTheory.Cartier

theorem exists_sec_preimage {k : Type} [CommRing k] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {a n : ℕ} (ha : 0 < a)
    (f : X ⟶ PSpace k n) (iso : LBIso ((ProjSpace.O1 k n).pull f) (lbPow L a)) {S : Set (PSpace k n)} (hS : S.Finite) :
    ∃ m, 0 < m ∧ ∃ (s : (lbPow L m).Sec) (U : (PSpace k n).Opens), S ⊆ U ∧ Out.nonzeroLocus s = f ⁻¹ᵁ U := by
  obtain ⟨r, hr, t, ht, -, -⟩ := (isAmple_projective_O_one k n).exists_affine_finite_subset hS (U := ⊤) (Set.subset_univ _)
  have h1 := ProjSpace.O1_isLB k n
  obtain ⟨t₁, e₁⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow (LB.isLB_pull h1 f) r)
    (LB.isLB_pull (isLB_lbPow h1 r) f) (lbIso_lbPow_pull h1 f r) (GlobalTheory.secPull t f)
  obtain ⟨t₂, e₂⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow (isLB_lbPow hL a) r)
    (isLB_lbPow (LB.isLB_pull h1 f) r) (lbIso_lbPow iso r).symm t₁
  obtain ⟨t₃, e₃⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow hL (a * r))
    (isLB_lbPow (isLB_lbPow hL a) r) (lbIso_lbPow_lbPow hL a r).symm t₂
  exact ⟨a * r, Nat.mul_pos ha hr, t₃, _, ht, by rw [e₃, e₂, e₁, GlobalTheory.nonzeroLocus_secPull]⟩

theorem exists_cut {k : Type} [CommRing k] {X : Scheme.{0}} [IsLocallyNoetherian X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {L : LB X} (hL : L.IsLB) (hL' : ∀ m, (lbPow L m).IsLB) {a n : ℕ} (ha : 0 < a)
    (f : X ⟶ PSpace k n) (hf : f ≫ PSpace.str k n = p) (iso : LBIso ((ProjSpace.O1 k n).pull f) (lbPow L a))
    {B : Set X} (hB : IsClosed B) {z : X} {e : ℕ}
    (h₁ : topologicalKrullDim (closure ({z} : Set X)) = (e + 1 + 2 : ℕ))
    (h₂ : topologicalKrullDim (f '' (closure {z} ∩ B)) + 3 ≤ (e + 1 + 2 : ℕ))
    (h₃ : CharZero (X.residueField z) → z ∉ B) :
    ∃ m, 0 < m ∧ ∃ s : (lbPow L m).Sec, z ∈ Out.nonzeroLocus s ∧ ∀ w, cutMult (hL' m) s z w ≠ 0 →
      topologicalKrullDim (closure ({w} : Set X)) = (e + 2 : ℕ) ∧
      topologicalKrullDim (f '' (closure {w} ∩ B)) + 3 ≤ (e + 2 : ℕ) ∧ (CharZero (X.residueField w) → w ∉ B) := by
  have := hX.isNoetherian
  have : IsProper f := by
    obtain ⟨N, jN, _, hjN⟩ := hX.isProjOver
    have := isProper_str k N
    have := isProper_str k n
    have : IsProper p := hjN ▸ inferInstance
    have : IsProper (f ≫ PSpace.str k n) := hf ▸ this
    exact IsProper.of_comp f (PSpace.str k n)
  have hC : IsClosed (closure {z} ∩ B) := isClosed_closure.inter hB
  obtain ⟨G, hG, hGC, hGs⟩ := exists_finite_specializes hC
  obtain ⟨m, hm, s, U, hU, hs⟩ := exists_sec_preimage hL ha f iso ((hG.insert z).image f)
  have hGU : ∀ g ∈ G, f g ∈ U := fun g hg => hU ⟨g, Or.inr hg, rfl⟩
  refine ⟨m, hm, s, hs ▸ hU ⟨z, Or.inl rfl, rfl⟩, fun w hw => ?_⟩
  obtain ⟨w', hw', hco, hwU⟩ := exists_of_cutMult_ne_zero _ s hw
  rw [hs] at hwU
  replace hwU : f w ∉ U := hwU
  have emb := (redι (clo z)).isClosedEmbedding
  have hzw : z ⤳ w := specializes_iff_mem_closure.2 (by
    have : w ∈ Set.range (redι (clo z)) := ⟨w', hw'⟩
    rwa [range_redι] at this)
  refine ⟨?_, ?_, fun hw0 hwB => ?_⟩
  · have hZ := (topologicalKrullDim_eq_of_isEmbedding emb.isEmbedding (range_redι _)).symm.trans h₁
    have h := dim_closure_of_coheight hX (redι (clo z)) (n := e + 2) hZ hco
    rw [← h]
    refine topologicalKrullDim_eq_of_isEmbedding (emb.isEmbedding.comp IsEmbedding.subtypeVal) ?_
    rw [Set.range_comp, Subtype.range_coe, ← emb.closure_image_eq, Set.image_singleton, hw']
  · have hfC : IsClosed (f '' (closure {z} ∩ B)) := f.isClosedMap _ hC
    have h₄ := topologicalKrullDim_add_one_le (hfC.sdiff U.isOpen) hfC (by
      rintro _ ⟨⟨x, hx, rfl⟩, -⟩
      obtain ⟨g, hg, hgx⟩ := hGs x hx
      exact ⟨f g, ⟨g, hGC hg, rfl⟩, fun h => h.2 (hGU g hg), hgx.map f.continuous⟩)
    have h₅ : f '' (closure {w} ∩ B) ⊆ f '' (closure {z} ∩ B) \ U := by
      rintro _ ⟨x, ⟨hx, hxB⟩, rfl⟩
      have hwx : w ⤳ x := specializes_iff_mem_closure.2 hx
      exact ⟨⟨x, ⟨specializes_iff_mem_closure.1 (hzw.trans hwx), hxB⟩, rfl⟩,
        fun h => hwU ((hwx.map f.continuous).mem_open U.isOpen h)⟩
    have h₆ := (IsEmbedding.inclusion h₅).isInducing.topologicalKrullDim_le
    refine GlobalTheory.PullVanish.withBot_le_of_add_one_le ?_
    calc topologicalKrullDim (f '' (closure {w} ∩ B)) + 3 + 1
        = topologicalKrullDim (f '' (closure {w} ∩ B)) + 1 + 3 := add_right_comm _ _ _
      _ ≤ topologicalKrullDim (f '' (closure {z} ∩ B)) + 3 := by
        gcongr
        exact le_trans (by gcongr) h₄
      _ ≤ _ := h₂
  · have hzB := h₃ (charZero_of_specializes hzw hw0)
    obtain ⟨g, hg, hgw⟩ := hGs w ⟨specializes_iff_mem_closure.1 hzw, hwB⟩
    obtain ⟨g', rfl⟩ : g ∈ Set.range (redι (clo z)) := by
      rw [range_redι]
      exact (hGC hg).1
    subst hw'
    have l₁ : w' < g' := ⟨emb.isInducing.specializes_iff.1 hgw, fun h =>
      hwU (((show w' ⤳ g' from h).map (redι (clo z) ≫ f).continuous).mem_open U.isOpen (hGU _ hg))⟩
    have l₂ : g' < genericPoint _ := ⟨genericPoint_specializes g', fun h => hzB (by
      have := ((show g' ⤳ genericPoint _ from h).map emb.continuous).mem_closed hB (hGC hg).2
      rwa [GlobalTheory.PullVanish.redι_genericPoint] at this)⟩
    have h₄ := Order.coheight_add_one_le l₁
    have h₅ := Order.coheight_add_one_le l₂
    rw [hco] at h₄
    have h₆ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₅) 1).trans h₄
    exact absurd h₆ (by decide)

end Cut

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec

theorem isClosed_bd {D : D7} {O : Setup D} {c : O.s.Comp} (M : DRBase O c) : IsClosed M.bd := by
  have := M.ar.isNoetherianRing
  have := isNoetherian_of_isProjOver O.s.T.Z.proj
  exact ((GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian O.s.T.Z.t.G O.s.T.Z.t.semi).preimage
    M.b.continuous).isClosed_compl

theorem exists_cuts : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (I : M.Emb) (z : M.B) (e : ℕ), I.Good z (e + 1) → ∃ m : ℕ, 0 < m ∧ ∃ s : (lbPow M.lamB m).Sec, I.Cuts s z e := by
  intro D O c M I z e h
  exact exists_cut M.ar (M.lam 2).isLB M.isLB_pow I.a_pos I.f I.f_str I.iso (isClosed_bd M) h.1 h.2.1 h.2.2

end GlobalTheory.VdmRec.CutSec

end
