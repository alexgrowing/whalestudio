import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmpleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.SiegelRingChange

noncomputable section
namespace GlobalTheory.SiegelFamilyBaseChange

theorem pb_iff {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
    {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {c : SiegPre h k ζ s}
    {c' : SiegPre h k ζ' s'} {f : S' ⟶ S} (H : SiegPB c' c f) (c'' : SiegPre h k ζ'' s'') (f' : S'' ⟶ S') :
    SiegPB c'' c' f' ↔ SiegPB c'' c (f' ≫ f) :=
  (GlobalTheory.SiegelPullComp.id_comp_cancel h k B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f').2 H

theorem quasiCompact_of_isQProjOver {o : Type} [CommRing o] {X : Scheme.{0}} {f : X ⟶ Sp o} (h : IsQProjOver f) :
    QuasiCompact f := by
  obtain ⟨N, i, -, hi, rfl⟩ := h
  have : IsProper (PSpace.str o N) := isProper_str o N
  infer_instance

theorem injective_of_isAlgebraic {o O : Type} [CommRing o] [IsDomain o] [CommRing O] [CharZero O]
    (ha : Algebra.IsAlgebraic ℤ o) (ψ : o →+* O) : Function.Injective ψ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  refine Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker ψ) hx0 hx (ha.1 x) ?_
  rw [eq_bot_iff]
  intro n hn
  simpa [Ideal.mem_comap, RingHom.mem_ker] using hn

theorem dense_generic {o O : Type} [CommRing o] [CommRing O] [IsDomain O] (ψ : o →+* O)
    (hψ : Function.Injective ψ) : Dense {x : Sp O | (spMap ψ x).asIdeal = ⊥} := by
  let x₀ : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  have hx₀ : Dense ({x₀} : Set (PrimeSpectrum O)) := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp [x₀]
  refine Dense.mono (s₁ := ({x₀} : Set (Sp O))) ?_ hx₀
  rintro x rfl
  exact Ideal.comap_bot_of_injective ψ hψ

variable {h k : ℕ} {o B : Type} [CommRing o] [CommRing B] {ζ : o} {ζ' : B}

theorem rep_baseChange (F : SFam h k ζ) (j : o →+* B) (hj : j ζ = ζ')
    (U : SiegPre h k ζ' (pullback.snd F.s (spMap j))) (hU : SiegPB U F.univ (pullback.fst F.s (spMap j)))
    {S : Scheme.{0}} (s' : S ⟶ Sp B) (c : SiegPre h k ζ' s') (hr : IsReduced S)
    (hd : Dense {x : S | ((s' ≫ spMap j) x).asIdeal = ⊥}) (hp : c.Principal) :
    ∃ f : S ⟶ pullback F.s (spMap j), f ≫ pullback.snd F.s (spMap j) = s' ∧ SiegPB c U f := by
  obtain ⟨g, hg, H⟩ := F.rep S _ (down j hj c) hr hd hp
  refine ⟨pullback.lift g s' hg, pullback.lift_snd _ _ _, (pb_iff hU c _).2 ?_⟩
  rw [pullback.lift_fst]
  exact H

theorem inj_baseChange (F : SFam h k ζ) (j : o →+* B) (hj : j ζ = ζ')
    (U : SiegPre h k ζ' (pullback.snd F.s (spMap j))) (hU : SiegPB U F.univ (pullback.fst F.s (spMap j)))
    {R : Type} [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ pullback F.s (spMap j)) (s' : Sp R ⟶ Sp B)
    (c : SiegPre h k ζ' s') (e : x ≫ pullback.snd F.s (spMap j) = y ≫ pullback.snd F.s (spMap j))
    (hx : SiegPB c U x) (hy : SiegPB c U y) : x = y := by
  refine pullback.hom_ext ?_ e
  refine F.inj R _ _ _ (down j hj c) ?_ ((pb_iff hU c _).1 hx) ((pb_iff hU c _).1 hy)
  simp only [Category.assoc, pullback.condition]
  rw [reassoc_of% e]

theorem exists_siegelFamily : Out.Laws → Out.Laws2 → ∀ (h k p : ℕ) (o : Type) [CommRing o] (ζ : o) (j : o →+* ZP p k), Odd k → 3 ≤ k → p.Prime → Function.Injective j → j ζ = zetaZP p k → (∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p k)), y = constPt y) → Algebra.IsAlgebraic ℤ o → SFam h k ζ → ∃ Ag : SiegelFamily h p k, SRep Ag := by
  intro L₁ L₂ h k p o _ ζ j hodd hk hpp hinj hj hc ha F
  have hpull := siegPre_pull_ringChange h k o (ZP p k) ζ (zetaZP p k) j F.X (pullback F.s (spMap j)) F.s
    (pullback.snd F.s (spMap j)) (pullback.fst F.s (spMap j)) hj pullback.condition
  obtain ⟨U, hU⟩ := hpull.1 F.univ
  have hUp : U.Principal := hpull.2.1 _ _ hU F.princ
  have := F.smooth
  have := F.isSeparated
  have := quasiCompact_of_isQProjOver F.qproj
  have : IsDomain o := hinj.isDomain j
  have hsm : SmoothOfRelativeDimension (h * (h + 1) / 2) (pullback.snd F.s (spMap j)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) F.smooth
  refine ⟨⟨pullback F.s (spMap j), pullback.snd F.s (spMap j), hsm, inferInstance, U, hUp, ?_, ?_⟩,
    (inferInstance : IsSeparated (pullback.snd F.s (spMap j))), ?_⟩
  · intro C O _ _ _ _ _ _ _ _ hO hpn β c hgen hsp
    have hp : c.Principal := GlobalTheory.T.principal_siegel_of_generic_principal_special_ample L₁ L₂ h k hodd hk _ _ C O hO p hpp hpn β c hgen hsp
    have : IsDomain O := hO.1.isDomain (algebraMap O C)
    have : CharZero O := RingHom.charZero (algebraMap O C)
    refine rep_baseChange F j hj U hU _ c inferInstance ?_ hp
    rw [← spMap_comp']
    exact dense_generic _ (injective_of_isAlgebraic ha _)
  · intro K _ x c h₁ h₂
    refine inj_baseChange F j hj U hU x _ _ c ?_ h₁ h₂
    rw [hc K (x ≫ _)]
    simp only [constPt, Category.assoc]
  · intro S s' c hr hd hp
    refine rep_baseChange F j hj U hU s' c hr (hd.mono fun x hx => ?_) hp
    have hx' : (s' x).asIdeal = ⊥ := hx
    change ((s' x).asIdeal).comap j = ⊥
    rw [hx']
    exact Ideal.comap_bot_of_injective j hinj

end GlobalTheory.SiegelFamilyBaseChange
end
