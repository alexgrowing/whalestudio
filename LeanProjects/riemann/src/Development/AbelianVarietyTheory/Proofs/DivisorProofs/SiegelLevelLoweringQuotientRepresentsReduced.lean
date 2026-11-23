import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleDeeperLevelSiegelCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculusStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChangeStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.QuotFamRep

theorem spMap_rid (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

section Calc

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
  {d d' d'' : ℕ}

theorem sRel_comp (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂

theorem sRel_cancel (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂

theorem sRel_principal (h₁ : SRel c' c d' d f) (hc : c.Principal) : c'.Principal :=
  (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 S') d d' d' h₁).2.1 hc

theorem sRel_scale (h₁ : SRel c' c 1 1 f) (e : ℕ) : SRel c' c e e f := by
  simpa using (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 S') 1 1 1 h₁).2.2 e

end Calc

theorem exists_pull {h k : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (c : SiegPre h k ζ s) (f : S' ⟶ S) : ∃ c' : SiegPre h k ζ (f ≫ s), SiegPB c' c f :=
  (GlobalTheory.T.siegelPre_pullback_principal_ringChange h k B B ζ ζ (RingHom.id B) S S' s (f ≫ s) f rfl (by rw [spMap_rid, Category.comp_id])).1 c

theorem asIdeal_eq_bot_iff {A A' : Type} [CommRing A] [CommRing A'] [IsDomain A] [IsDomain A'] (j : A →+* A')
    (hj : Function.Injective j) (hf : IsFinite (spMap j)) (y : Sp A') :
    ((spMap j) y).asIdeal = ⊥ ↔ y.asIdeal = ⊥ := by
  algebraize [j]
  have hm : Module.Finite A A' := by rw [IsFinite.SpecMap_iff] at hf; exact hf
  have : Algebra.IsIntegral A A' := inferInstance
  show Ideal.comap (algebraMap A A') y.asIdeal = ⊥ ↔ _
  refine ⟨fun e => Ideal.eq_bot_of_comap_eq_bot e, fun e => ?_⟩
  rw [e]; exact Ideal.comap_bot_of_injective (algebraMap A A') hj

end GlobalTheory.QuotFamRep

namespace GlobalTheory

open QuotFamRep in

theorem quotFam_represents : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N) (Q : SQuot F n (zetaAway n) j), 3 ≤ n → Odd N → n ∣ N → Function.Injective j → j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Surjective (spMap j) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Q.X, f ≫ Q.s = s' ∧ SiegPB c Q.univ f := by
  intro h n N F j Q hn hN hnN hj hjz hfin het hsurj S s' c hS hd hc
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hn0 : n ≠ 0 := by omega

  let S' := pullback s' (spMap j)
  let q : S' ⟶ S := pullback.fst s' (spMap j)
  let t : S' ⟶ Sp (cycAway N) := pullback.snd s' (spMap j)
  have hq := GlobalTheory.T.siegelPre_pullback_principal_ringChange h n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n) (RingHom.id _) S S' s' (t ≫ spMap j) q
    rfl (by rw [spMap_rid, Category.comp_id]; exact pullback.condition)
  obtain ⟨c', hc'⟩ := hq.1 c
  have hc'P : c'.Principal := hq.2.1 c c' hc' hc

  obtain ⟨S₁, π₁, C, hπf, hπe, hπs, hCrel, -⟩ := GlobalTheory.T.exists_finite_etale_deeper_level_siegel_cover h n N (cycAway n) (cycAway N) (zetaAway n)
    (cycBase hN0) j S' t c' hn hN hnN (by rw [cycBase_ζ]; exact hjz) hc'P
  let p : S₁ ⟶ S := π₁ ≫ q
  have : IsFinite p := by dsimp [p, q]; infer_instance
  have : Etale p := by dsimp [p, q]; infer_instance
  have : Surjective p := by dsimp [p, q]; infer_instance
  have hp : p ≫ s' = (π₁ ≫ t) ≫ spMap j := by
    simp only [p, q, t, Category.assoc, pullback.condition]
  have hred : IsReduced S₁ := GlobalTheory.isReduced_of_smooth_of_isReduced p
  have hden : Dense {x : S₁ | ((π₁ ≫ t) x).asIdeal = ⊥} := by
    have : UniversallyOpen p := UniversallyOpen.of_flat p
    have e : ∀ x, s' (p x) = spMap j ((π₁ ≫ t) x) := fun x => by
      rw [← Scheme.Hom.comp_apply, hp, Scheme.Hom.comp_apply]
    convert hd.preimage p.isOpenMap using 1
    ext x
    show ((π₁ ≫ t) x).asIdeal = ⊥ ↔ (s' (p x)).asIdeal = ⊥
    rw [e, asIdeal_eq_bot_iff j hj hfin]
  have hCP : C.Principal := sRel_principal hCrel hc'P
  obtain ⟨f₁, hf₁s, hf₁⟩ := F.rep S₁ (π₁ ≫ t) C hred hden hCP

  obtain ⟨c₀, hC0, h0C⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N (cycAway n) (cycAway N) (zetaAway n) (zetaAway N) j S₁ (π₁ ≫ t) C hN0
    (isUnit_natCast hN0) hnN hjz
  have hf₁N : SRel C F.univ (N / n) (N / n) f₁ := sRel_scale ((sRel_one_one_iff _ _ _).2 hf₁) _
  have h0F : SRel c₀ F.univ 1 (N / n) f₁ := by simpa using sRel_comp hf₁N h0C
  obtain ⟨g, hg⟩ : ∃ g : S₁ ⟶ Q.X, g = f₁ ≫ Q.π := ⟨_, rfl⟩
  have hgQ : SRel C Q.univ (N / n) 1 g := hg ▸ sRel_comp Q.low hf₁N
  have h0Q : SiegPB c₀ Q.univ g := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_comp hgQ h0C)
  have hCc : SRel C c (N / n) 1 p := sRel_comp ((sRel_one_one_iff _ _ _).2 hc') hCrel
  have h0c₁ : SRel c₀ c 1 1 p := by simpa using sRel_comp hCc h0C
  have hf₁p : f₁ ≫ F.s ≫ spMap j = p ≫ s' := by rw [← Category.assoc, hf₁s, hp]
  have hgs : g ≫ Q.s = p ≫ s' := by rw [hg, Category.assoc, Q.base]; exact hf₁p

  have key : pullback.fst p p ≫ g = pullback.snd p p ≫ g := by
    have : IsReduced (pullback p p) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst p p)
    have : IsSeparated Q.s := isSeparated_of_isQProjOver Q.qproj
    refine (GlobalTheory.hom_eq_iff_forall_isAlgClosed Q.s ?_).2 fun K _ _ x => ?_
    · simp only [Category.assoc, hgs, pullback.condition_assoc]
    obtain ⟨cx, hcx⟩ := exists_pull c₀ (x ≫ pullback.fst p p)
    have hx₁ := (sRel_one_one_iff _ _ _).2 hcx
    have hx₂ : SRel cx c₀ 1 1 (x ≫ pullback.snd p p) := by
      refine sRel_cancel h0c₁ ?_
      have := sRel_comp h0c₁ hx₁
      convert this using 1
      rw [Category.assoc, Category.assoc, pullback.condition]
    have e := Q.fibre K (x ≫ pullback.fst p p ≫ f₁) (x ≫ pullback.snd p p ≫ f₁) _ cx
      (by simp only [Category.assoc, hf₁p, pullback.condition_assoc])
      (by simpa only [Category.assoc] using sRel_comp h0F hx₁)
      (by simpa only [Category.assoc] using sRel_comp h0F hx₂)
    simpa only [hg, Category.assoc] using e
  have hcoeq : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ S₁), g₁ ≫ p = g₂ ≫ p → g₁ ≫ g = g₂ ≫ g := fun g₁ g₂ e => by
    have := pullback.lift g₁ g₂ e ≫= key
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  have hfac : p ≫ EffectiveEpi.desc p g hcoeq = g := EffectiveEpi.fac p g hcoeq
  refine ⟨EffectiveEpi.desc p g hcoeq, ?_, ?_⟩
  · rw [← cancel_epi p, ← Category.assoc, hfac, hgs]
  · exact GlobalTheory.T.siegPB_of_finite_etale_surjective_cover h n (cycAway n) (cycBase hn0) S S₁ Q.X s' ((π₁ ≫ t) ≫ spMap j) Q.s c c₀ Q.univ p _ hn
      (hN.of_dvd_nat hnN) Q.princ inferInstance inferInstance inferInstance ((sRel_one_one_iff _ _ _).1 h0c₁)
      (hfac.symm ▸ h0Q)

end GlobalTheory
