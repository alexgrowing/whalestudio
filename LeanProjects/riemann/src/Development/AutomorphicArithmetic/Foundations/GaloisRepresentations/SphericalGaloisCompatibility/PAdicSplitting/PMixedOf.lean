import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.InfLifts
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorOfMono0
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

namespace UpperTheory.Gal.ToralGalois.R2

private theorem fixed_ne_bot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : ρ.Equiv σ) {H : Subgroup G} (h : fixed ρ H ≠ ⊥) : fixed σ H ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨φ.toIntertwiningMap v, GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_, fun e => h0 ?_⟩
  · rw [← φ.toIntertwiningMap.isIntertwining, GlobalTheory.Parabolic.mem_fixed.1 hv g hg]
  · exact φ.toLinearEquiv.injective (e.trans (map_zero φ.toLinearEquiv).symm)

private theorem pairwise_of_map {α β : Type*} (f : α → β) {r : β → β → Prop} (hr : Symmetric r) (t : Multiset α)
    (h : (t.map f).Pairwise r) : t.Pairwise fun a b => r (f a) (f b) := by
  induction t using Quot.inductionOn with
  | h l =>
    have h' : Multiset.Pairwise r ((l.map f : List β) : Multiset β) := h
    haveI : Std.Symm r := ⟨fun _ _ e => hr e⟩
    rw [Multiset.pairwise_coe_iff_pairwise, List.pairwise_map] at h'
    exact ⟨l, rfl, h'⟩

private theorem apart_of_nu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s : Multiset (IrrGL k)} (c : ℂ)
    (h : ((s.map fun y => y.nu c).filter fun y => 2 ≤ y.1).Pairwise fun y z => ¬ y.Inert z) :
    (s.filter fun y => 2 ≤ y.1).Pairwise fun y z => ¬ y.Inert z := by
  rw [Multiset.filter_map] at h
  have hsym : Symmetric fun y z : IrrGL k => ¬ y.Inert z :=
    fun y z hyz e => hyz (IrrGL.inert_equivalence.symm e)
  obtain ⟨l, hl, hp⟩ := pairwise_of_map (t := s.filter fun y => 2 ≤ y.1) (fun y => y.nu c) hsym (by convert h using 3; exact Iff.rfl)
  refine ⟨l, hl, hp.imp fun {y z} hyz e => hyz ?_⟩
  exact IrrGL.inert_equivalence.trans (IrrGL.inert_equivalence.symm (IrrGL.inert_nu y c))
      (IrrGL.inert_equivalence.trans e (IrrGL.inert_nu z c))

end UpperTheory.Gal.ToralGalois.R2

open GlobalTheory.PlainMono in
theorem UpperTheory.Gal.ToralGalois.R2.mixedOf :
    MixedOf := by
  intro E Ω _ _ _ _ _ _ n π w σ hσ hfix hap A h rc hrc hm
  obtain ⟨a, ha, L⟩ := hrc
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hg : IsGeneric σ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E n π w σ hσ
  have hnu : ∀ (z : IrrGL (w.adicCompletion E)) (s : ℂ), IsGeneric z.rep → IsGeneric (z.nu s).rep :=
    fun z s hz => (isGeneric_congr (IrrGL.twEquiv z _ _)).1 ((isGeneric_twist_iff _).2 hz)
  have hgτ : IsGeneric (algNorm σ).rep :=
    hnu _ _ ((isGeneric_congr (IrrGL.equivOf σ.ρ σ.smooth σ.irred)).1 hg)
  obtain ⟨c, Δ, y, hd, hun, hL, ⟨e⟩⟩ := GlobalTheory.genericUnlinkedGL_outright (w.adicCompletion E) (algNorm σ).1 _
    (algNorm σ).rep (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr hgτ
  have hIsL : IsL ((List.ofFn Δ : List (Segment (w.adicCompletion E))) : Multiset (Segment (w.adicCompletion E)))
      (algNorm σ).rep :=
    ⟨c, y, hd, ⟨Δ, ⟨Fin.univ_val_map Δ, fun i j hij hp => hun i j hij.ne hp.1⟩, hL⟩,
      (isCosocle_self (algNorm σ).2.rep.irr).of_equiv (.refl _) e⟩
  have hm' := hm
  rw [L.langlands (List.ofFn Δ) (algNorm σ) hIsL, segSum] at hm'
  have hlen : ∀ i, (Δ i).len = 1 := by
    intro i
    have hmi := GlobalTheory.UnlinkedMono.noMonodromy_of_mem_weilDeligneListSum _ hm' _
      (List.mem_map.2 ⟨Δ i, List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩)
    by_contra hne
    have hirr : IsIrrWD ((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2)) := by
      rw [← L.nu]; exact L.cusp _ ((Δ i).isCusp_first.nu _)
    exact GlobalTheory.SegLen.not_mono0_lpChar_lpSp hirr (by have := (Δ i).len_pos; omega) hmi
  obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh (w.adicCompletion E) (IrrGL.of σ.ρ σ.smooth σ.irred)
  obtain ⟨s, hs⟩ : ∃ s, HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep s :=
    ⟨_, GlobalTheory.LocGL.hasSupport_msupp_of_isL UpperTheory.Zero.LLC.Pr.zel _ 𝔪 _ h𝔪⟩
  have hs' := GlobalTheory.LocGL.SupportRing.hasSupport_nu hs (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  have hms := GlobalTheory.LocGL.ZelevinskyExpansion.msupp_eq_of_isL (algNorm σ).2.rep.irr hIsL hs'
  have mem : ∀ u ∈ s, ∃ i, (Δ i).first = u.nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := by
    intro u hu
    have hu' : u.nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) ∈ msupp ((List.ofFn Δ : List (Segment (w.adicCompletion E))) :
        Multiset (Segment (w.adicCompletion E))) := by
      rw [hms]; exact Multiset.mem_map_of_mem _ hu
    rw [msupp, Multiset.mem_bind] at hu'
    obtain ⟨D, hD, hu''⟩ := hu'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (Multiset.mem_coe.1 hD)
    rw [Segment.mem_ms, Segment.mem_carrier] at hu''
    obtain ⟨m, hm1, e'⟩ := hu''
    have : m = 0 := by have := hlen i; omega
    subst this
    exact ⟨i, by simpa using e'⟩
  refine ⟨fixed_ne_bot (IrrGL.equivOf σ.ρ σ.smooth σ.irred) hfix, s, hs, ?_, apart_of_nu _ (hap _ hs')⟩
  intro y1 hy1 z1 hz1 hyz
  obtain ⟨i, hi⟩ := mem y1 hy1
  obtain ⟨j, hj⟩ := mem z1 hz1
  have key : (Δ i).first = (Δ j).first.nu 1 := by
    rw [hi, hj, hyz, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]
  have hne := ne_nu_one L (Δ j).isCusp_first
  by_cases hij : i = j
  · subst hij; exact hne key
  · refine hun j i (Ne.symm hij) ?_
    rw [eq_single_of_len (hlen j), eq_single_of_len (hlen i)]
    exact linked_single _ _ hne key
