import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.AdicGeo

theorem lift_facts {X S Z Y : Scheme.{0}} (u : Y ⟶ X) (f : X ⟶ S) (g : Z ⟶ S) (fY : Y ⟶ S) (hf : u ≫ f = fY) :
    (IsOpenImmersion u → IsOpenImmersion (pullback.lift (pullback.fst fY g ≫ u) (pullback.snd fY g)
      (by rw [Category.assoc, hf, pullback.condition]) : pullback fY g ⟶ pullback f g)) ∧
    Set.range (pullback.lift (pullback.fst fY g ≫ u) (pullback.snd fY g)
      (by rw [Category.assoc, hf, pullback.condition]) : pullback fY g ⟶ pullback f g) =
      pullback.fst f g ⁻¹' Set.range u := by
  subst hf
  have key : (pullback.lift (pullback.fst (u ≫ f) g ≫ u) (pullback.snd (u ≫ f) g)
      (by rw [Category.assoc, pullback.condition]) : pullback (u ≫ f) g ⟶ pullback f g) =
      pullback.map (u ≫ f) g f g u (𝟙 Z) (𝟙 S) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp
  refine ⟨fun hu => ?_, ?_⟩
  · have hsq : IsPullback (pullback.lift (pullback.fst (u ≫ f) g ≫ u) (pullback.snd (u ≫ f) g)
        (by rw [Category.assoc, pullback.condition]) : pullback (u ≫ f) g ⟶ pullback f g)
        (pullback.fst (u ≫ f) g) (pullback.fst f g) u := by
      refine IsPullback.of_right (h₁₂ := pullback.snd f g) (h₂₂ := f) (v₁₃ := g) ?_ (by simp)
        (IsPullback.of_hasPullback f g).flip
      rw [pullback.lift_snd]
      exact (IsPullback.of_hasPullback (u ≫ f) g).flip
    exact MorphismProperty.of_isPullback hsq.flip hu
  · rw [key, Scheme.Pullback.range_map]
    simp

theorem isSum_lift {X S Z : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (u : ∀ s, Y s ⟶ X) (f : X ⟶ S) (g : Z ⟶ S)
    (fY : ∀ s, Y s ⟶ S) (hf : ∀ s, u s ≫ f = fY s) (h : IsSum u) :
    IsSum (fun s => (pullback.lift (pullback.fst (fY s) g ≫ u s) (pullback.snd (fY s) g)
      (by rw [Category.assoc, hf, pullback.condition]) : pullback (fY s) g ⟶ pullback f g)) := by
  obtain ⟨ho, hc, hd⟩ := h
  refine ⟨fun s => (lift_facts (u s) f g (fY s) (hf s)).1 (ho s), fun x => ?_, fun s s' hss' => ?_⟩
  · obtain ⟨s, hs⟩ := hc (pullback.fst f g x)
    refine ⟨s, ?_⟩
    rw [(lift_facts (u s) f g (fY s) (hf s)).2]
    exact hs
  · rw [(lift_facts (u s) f g (fY s) (hf s)).2, (lift_facts (u s') f g (fY s') (hf s')).2]
    exact (hd s s' hss').preimage _

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev str (M : Model l K) : GlobalTheory.Et.geom (PadicAlgCl l) M.q ⟶ Spec (CommRingCat.of (PadicAlgCl l)) :=
  pullback.snd M.q (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))

theorem isSum_geom {M : Model l K} {r : ℕ} {P : Fin r → Model l K} (u : ∀ a, (P a).X ⟶ M.X)
    (hu : ∀ a, u a ≫ M.p = (P a).p) (h : IsSum u) :
    IsSum (fun a => GlobalTheory.Et.geomMap (PadicAlgCl l) (P a).q (Model.genMap (u a) (hu a)) (Model.genMap_q (u a) (hu a))) :=
  isSum_lift (fun a => Model.genMap (u a) (hu a)) M.q _ (fun a => (P a).q) (fun a => Model.genMap_q (u a) (hu a))
    (isSum_lift u M.p _ (fun a => (P a).p) hu h)

theorem proper_p {M : Model l K} (h : M.Good) : IsProper M.p := by
  obtain ⟨N, i, hi, e⟩ := h.1
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (OK l K) N
  rw [← e]
  infer_instance

theorem proper_str {M : Model l K} (h : M.Good) : IsProper (str M) := by
  have := proper_p h
  infer_instance

theorem comp_str {M : Model l K} (h : M.Good) {d : ℕ} (hc : M.Conn d) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (s : Fin r) :
    IsProper (j s ≫ str M) ∧ SmoothOfRelativeDimension d (j s ≫ str M) := by
  obtain ⟨ho, hcov, hd⟩ := hj
  have := ho s
  have := proper_str h
  constructor
  · have hcl : IsClosed (Set.range (j s)) := by
      have : Set.range (j s) = (⋃ t ∈ ({s}ᶜ : Set (Fin r)), Set.range (j t))ᶜ := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
        constructor
        · intro hx t hts hxt
          exact Set.disjoint_left.1 (hd s t (Ne.symm hts)) hx hxt
        · intro hx
          obtain ⟨t, ht⟩ := hcov x
          by_cases hts : t = s
          · exact hts ▸ ht
          · exact absurd ht (hx t hts)
      rw [this, isClosed_compl_iff]
      exact isOpen_biUnion fun t _ => (ho t).base_open.isOpen_range
    have : IsClosedImmersion (j s) := .of_isPreimmersion _ hcl
    infer_instance
  · have h1 : SmoothOfRelativeDimension d M.q := hc.2
    have := smoothOfRelativeDimension_isStableUnderBaseChange d
    have h2 : SmoothOfRelativeDimension d (str M) :=
      MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension d) _ _ h1
    have h3 := smoothOfRelativeDimension_comp (n := 0) (m := d) (j s) (str M)
    rwa [zero_add] at h3

theorem unit_of_over {Ω : Type} [Field Ω] [CharZero Ω] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of Ω)) (q : ℕ)
    [NeZero q] : IsUnit (q : Γ(Y, ⊤)) := by
  have h : IsUnit (q : Ω) := (Nat.cast_ne_zero.2 (NeZero.ne q)).isUnit
  simpa using h.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ f.appTop).hom

theorem prim_of_over {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of Ω))
    (q : ℕ) [NeZero q] : Nonempty (GlobalTheory.EtC.Prim q Γ(Y, ⊤)) := by
  have hdeg : (Polynomial.cyclotomic q Ω).degree ≠ 0 := (Polynomial.degree_cyclotomic_pos q Ω (NeZero.pos q)).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  have h0 : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ
  exact ⟨GlobalTheory.EtC.Prim.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ f.appTop).hom
    ⟨ζ, (Nat.cast_ne_zero.2 (NeZero.ne q)).isUnit, h0⟩⟩

theorem inv_sch (q : ℕ) {Y : Scheme.{0}} (h : IsUnit (q : Γ(Y, ⊤))) : GlobalTheory.EtC.Inv q (GlobalTheory.EtC.sch.obj Y) := by
  intro U ⟨x⟩
  change U ⟶ Y at x
  simpa using h.map x.appTop.hom

end CrystallineSemistableComparison.AdicGeo
