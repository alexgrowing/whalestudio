import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutUnr

section Fixed
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_fixed_of_mem_biSup (ρ : Representation ℂ (GQ L n) W) (K : Set (GAf L n))
    (t : Finset (Submodule ℂ (GAf L n → W))) :
    (∀ S ∈ t, NG.IsIrrRep ρ S) → ∀ f ∈ ⨆ S ∈ t, S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) →
      ∃ S ∈ t, ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ g = g := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    exact absurd hf hf0
  | insert S t hS ih =>
    intro ht f hf hf0 hfix
    have ht' : ∀ S' ∈ t, NG.IsIrrRep ρ S' := fun S' h => ht S' (Finset.mem_insert_of_mem h)
    have hSi := ht S (Finset.mem_insert_self _ _)
    have hNst : ∀ h, ∀ g ∈ ⨆ S' ∈ t, S', NG.rt L n h g ∈ ⨆ S' ∈ t, S' := by
      intro h
      have hle : (⨆ S' ∈ t, S') ≤ (⨆ S' ∈ t, S').comap (NG.rt L n h) := by
        refine iSup₂_le fun S' hS' g hg => ?_
        exact (le_iSup₂ (f := fun (S'' : Submodule ℂ (GAf L n → W)) (_ : S'' ∈ t) => S'') S' hS')
          ((ht' S' hS').1.stable h g hg)
      exact fun g hg => hle hg
    rw [Finset.iSup_insert] at hf
    by_cases hd : S ⊓ (⨆ S' ∈ t, S') = ⊥
    · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
      have hfa : ∀ κ ∈ K, NG.rt L n κ a = a ∧ NG.rt L n κ b = b := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add] at e
        have h1 : NG.rt L n κ a - a = b - NG.rt L n κ b := by
          rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
        have hm : NG.rt L n κ a - a ∈ S ⊓ (⨆ S' ∈ t, S') :=
          ⟨S.sub_mem (hSi.1.stable κ a ha) ha, h1 ▸ Submodule.sub_mem _ hb (hNst κ b hb)⟩
        rw [hd, Submodule.mem_bot] at hm
        refine ⟨sub_eq_zero.1 hm, ?_⟩
        rw [hm] at h1
        exact (sub_eq_zero.1 h1.symm).symm
      by_cases ha0 : a = 0
      · subst ha0
        rw [zero_add] at hf0
        obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih ht' b hb hf0 fun κ hκ => (hfa κ hκ).2
        exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩
      · exact ⟨S, Finset.mem_insert_self _ _, a, ha, ha0, fun κ hκ => (hfa κ hκ).1⟩
    · have hsub : NG.IsSubrep ρ (S ⊓ (⨆ S' ∈ t, S')) :=
        ⟨inf_le_left.trans hSi.1.le, fun h g hg => ⟨hSi.1.stable h g hg.1, hNst h g hg.2⟩⟩
      have heq : S ⊓ (⨆ S' ∈ t, S') = S := (hSi.2.2 _ hsub inf_le_left).resolve_left hd
      have hSN : S ≤ ⨆ S' ∈ t, S' := heq ▸ inf_le_right
      have hfN : f ∈ ⨆ S' ∈ t, S' := (sup_le hSN le_rfl) hf
      obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih ht' f hfN hf0 hfix
      exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩

theorem exists_fixed_of_isoTyp (ρ : Representation ℂ (GQ L n) W) {S : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (K : Set (GAf L n)) {f : GAf L n → W} (hf : f ∈ NG.isoTyp ρ S)
    (hf0 : f ≠ 0) (hfix : ∀ κ ∈ K, NG.rt L n κ f = f) : ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ g = g := by
  unfold NG.isoTyp at hf
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  obtain ⟨S', hS', g, hg, hg0, hgf⟩ :=
    exists_fixed_of_mem_biSup ρ K s (fun S' h => (hs h).1) f hfs hf0 hfix
  obtain ⟨T, hT⟩ := (hs hS').2
  refine ⟨(T.symm ⟨g, hg⟩ : S), (T.symm ⟨g, hg⟩).2, ?_, fun κ hκ => ?_⟩
  · intro h0
    apply hg0
    have h1 : T.symm ⟨g, hg⟩ = 0 := Subtype.ext h0
    have h2 := congrArg T h1
    rw [LinearEquiv.apply_symm_apply, map_zero] at h2
    exact congrArg Subtype.val h2
  · set a := T.symm ⟨g, hg⟩
    have e := hT κ a ⟨NG.rt L n κ (a : GAf L n → W), hS κ _ a.2⟩ rfl
    have hTa : ((T a : _) : GAf L n → W) = g := by simp [a]
    rw [hTa, hgf κ hκ] at e
    have e2 : T ⟨NG.rt L n κ (a : GAf L n → W), hS κ _ a.2⟩ = T a := Subtype.ext (e.trans hTa.symm)
    exact congrArg Subtype.val (T.injective e2)

end Fixed

end GlobalTheory.AutUnr

namespace GlobalTheory.AutUnr

theorem mem_placesOver_of_overPl {D : D7} {p : ℕ} {w w' : PlE D.host}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hw : NG.OverPl w v) (hw' : NG.OverPl w' v)
    (h : w' ∈ placesOver D.host.E p) : w ∈ placesOver D.host.E p := by
  have h1 : ((p : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw', Ideal.mem_comap, map_natCast]; exact h
  rw [← hw, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem exists_splitPlace_eq (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  obtain ⟨s, -, h, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [GlobalTheory.SplitConjPlace.mem_conj_w]
  refine (h x _ ?_).symm
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem locV_unr : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), IsSplitPl D.host w → w ∉ X.nd.Q i → (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) → D.naut.unr (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop P w hw hQ hg hp
  classical
  obtain ⟨s, hsw⟩ := exists_splitPlace_eq D w hw
  have hov : NG.OverPl w s.v := hsw ▸ s.w_under

  have hjf : X.nd.j i - 1 + 1 = X.nd.j i := by have := X.nd.j_range i; omega
  let jf : Fin D.R.m := ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩
  have h0 := hMI.hyp (X.nd.w i) jf
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)) :=
    GlobalTheory.FitHecke.hypOutside_transport' (M := M) (X.nd.mu_w i).symm hjf _ _ (X.nd.j_range i).1 (X.nd.j_range i).2 _ h0

  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQe : C.Q (X.nd.w i) = Sp.B.Qc (X.nd.j i) (X.nd.w i) := (Sp.Qc_eq _ _).symm
  have hvB : s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf) := by
    rintro (⟨w', hov', k, hk⟩ | hq)
    · exact hg k (mem_placesOver_of_overPl hov hov' hk)
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i) jf hq
      rcases hw' with hQ' | hp'
      · rw [hQe] at hQ'
        have hwQ : w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) := Sp.B.Qc_over _ _ w' w hQ' ⟨s.v, hov', hov⟩
        rw [← Sp.Q_eq _ _ i hi] at hwQ
        exact hQ hwQ
      · rw [X.nd.w_l i] at hp'
        exact hp (mem_placesOver_of_overPl hov hov' hp')

  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne P)
  have hfix : ∀ κ ∈ {κ : GAf D.host.E D.R.nV | κ ∈ Umax D.host.E D.R.nV ∧ TrivOutside {s.v} κ},
      NG.rt D.host.E D.R.nV κ ((mlX M X i).real y) = (mlX M X i).real y := by
    rintro κ ⟨hU, htr⟩
    have htr' : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf))ᶜ κ := by
      intro v hv
      apply htr v
      rintro rfl
      exact hv hvB
    obtain ⟨hJ, hχ⟩ := hyp κ htr'
    have hκ : κ ∈ (mlX M X i).J := hJ.2 hU
    have hmem : (mlX M X i).real y ∈ NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ := by
      rw [← (mlX M X i).real_range]; exact ⟨y, rfl⟩
    have e := hmem.2 ⟨κ, hκ⟩
    rw [hχ hκ] at e
    simpa using e
  have hr0 : (mlX M X i).real y ≠ 0 := fun h =>
    hy0 ((mlX M X i).real_inj (h.trans (map_zero _).symm))
  obtain ⟨f, hf, hf0, hff⟩ := exists_fixed_of_isoTyp (mlX M X i).wt.ρ (irr P).1.stable _ hy hr0 hfix
  have hsph : NG.AutRep.SphAt { (mlX M X i).wt with S := F P, irrS := irr P } s.v :=
    ⟨f, hf, hf0, fun κ hU htr => hff κ ⟨hU, htr⟩⟩
  rw [← hsw]
  exact A.au.locUnr _ _ _ _ s hsph

end GlobalTheory.AutUnr
