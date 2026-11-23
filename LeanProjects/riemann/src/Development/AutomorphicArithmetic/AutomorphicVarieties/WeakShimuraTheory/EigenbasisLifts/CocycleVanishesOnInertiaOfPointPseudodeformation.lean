import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.InertiaTrivialOfCharpolyRootsNearCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DblRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RootsNear
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.cocycle_vanishes_on_inertia_of_point_pseudodeformation :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (PadicAlgCl l)), r.V0ok → B.u.D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ) → Continuous ρ → ∀ y ∈ Z1 (Loc.adGL ρ), ∀ g ∈ V.frame.I0, y g = 0 := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hok hB hρ y hy g hg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Subsingleton.elim _ _
  haveI : Fact s.p.Prime := ⟨s.p_prime⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨hI0, hD0, g0, hg0D, hg0e⟩ := hok
  have hpv : ((s.p : ℕ) : 𝓞 (W.Lp L)) ∈ s.v0.asIdeal := by
    have h := Ideal.absNorm_mem s.v0.asIdeal
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← normV, s.norm_v0_eq_one] at h
  have hpw : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal := by
    rw [← s.hw s.v0]
    have h := (s.hA s.v0 _).mpr hpv
    simpa using h
  obtain ⟨j, hj⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := s.p)).1 (s.A s.v0) (s.w s.v0) (s.hw s.v0) hpw
  obtain ⟨-, φ, hφo, -, -, hφI, hφc, -⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := s.p)).2 j
  change g ∈ Subgroup.map V.pr (Ine (s.A s.v0)) at hg
  change ∀ i, Subgroup.map V.pr (Ine (s.A s.v0)) ≤ (r.chib i).ker at hI0
  change ∀ g ∈ Subgroup.map V.pr (Dec (s.A s.v0)), ∀ i j, (r.chib i) g = (r.chib j) g at hD0
  change g0 ∈ Subgroup.map V.pr (Dec (s.A s.v0)) at hg0D
  rw [← hj] at hg hI0 hD0 hg0D
  obtain ⟨ρ₂, hρ₂c, hρ₂p, hρ₂y⟩ := dblRep ρ hρ y hy
  let ψ : ↥(Dec (Loc.placeJ j)) →* V.frame.G₀ := V.pr.comp (Dec (Loc.placeJ j)).subtype
  have hψc : Continuous ψ := (V.pr_cont W.continuous_resP).comp continuous_subtype_val
  haveI : CompactSpace ↥(Dec (Loc.placeJ j)) := isCompact_iff_compactSpace.mp (isClosed_Dec (F := L) (Loc.placeJ j)).isCompact
  let κ : ↥(Dec (Loc.placeJ j)) →* (ResidueField c.O)ˣ := (r.chib ⟨0, hn⟩).comp ψ
  have main := inertia_trivial_of_charpoly_roots_near_character s.p_ne φ hφo c κ ?_ ?_ (ρ₂.comp ψ) (hρ₂c.comp hψc) ?_
  · obtain ⟨h, hh, rfl⟩ := hg
    apply hρ₂y
    exact main ⟨h, Ine_le_Dec _ hh⟩ ((hφI ⟨h, Ine_le_Dec _ hh⟩).2 hh)
  · intro h hh
    have hI : (h : G L Ω) ∈ Ine (Loc.placeJ j) := (hφI h).1 hh
    exact MonoidHom.mem_ker.mp (hI0 ⟨0, hn⟩ ⟨(h : G L Ω), hI, rfl⟩)
  · obtain ⟨h, hh, rfl⟩ := hg0D
    refine ⟨⟨h, hh⟩, fun heq => hg0e ?_⟩
    unfold Loc.cycA at heq
    rw [MonoidHom.comp_apply, hφc] at heq
    have e1 : V.frame.ε (V.frame.η.ker.subtype (V.pr h)) = cycZ L Ω l h := by
      change V.ε (toGS Ω V.S' (W.resP L Ω h)) = _
      rw [← MonoidHom.comp_apply, V.hε]
      rfl
    apply Units.ext
    unfold W.GFrame.eps W.pushCh
    change (algebraMap c.O (ResidueField c.O)) (algebraMap ℤ_[l] c.O
      ↑(V.frame.ε (V.frame.η.ker.subtype (V.pr h)))) = 1
    change (residue c.O) (algebraMap ℤ_[l] c.O ↑(cycZ L Ω l h)) = 1 at heq
    rw [e1, IsLocalRing.ResidueField.algebraMap_eq]
    exact heq
  · intro h a ha t ht
    change t ∈ (W.mat ρ₂ (ψ h)).charpoly.roots at ht
    rw [hρ₂p, Polynomial.roots_pow, Multiset.mem_nsmul] at ht
    refine rootsNear B x ρ hB (ψ h) a (fun i => ?_) t ht.2
    rw [ha]
    exact congrArg Units.val (hD0 (ψ h) ⟨h.1, h.2, rfl⟩ ⟨0, hn⟩ i)
