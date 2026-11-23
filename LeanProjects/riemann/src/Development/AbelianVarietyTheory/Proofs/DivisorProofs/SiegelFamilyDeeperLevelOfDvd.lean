import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleDeeperLevelSiegelCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculusStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegLev

section
variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {c : SiegPre h n ζ s}
  {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {d d' d'' : ℕ}

theorem sRel_trans (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂

theorem sRel_cancel (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂

theorem sRel_principal (h₁ : SRel c' c d' d f) (hc : c.Principal) : c'.Principal :=
  (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 _) d d' d' h₁).2.1 hc

theorem sRel_scale (h₁ : SRel c' c d' d f) (e : ℕ) : SRel c' c (d' * e) (d * e) f :=
  (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 _) d d' d' h₁).2.2 e

end

theorem spMap_id_eq (o : Type) [CommRing o] : spMap (RingHom.id o) = 𝟙 _ := Spec.map_id _

theorem sFam_of_dvd : ∀ (h n N : ℕ) (o : Type) [CommRing o] [IsNoetherianRing o] (b : TBase o N), 3 ≤ n → Odd N → n ∣ N →
    Nonempty (SFam h n ((b.ζ : o) ^ (N / n))) → Nonempty (SFam h N (b.ζ : o)) := by
  intro h n N o _ _ b hn hN hnN ⟨F⟩
  set ζ : o := (b.ζ : o) ^ (N / n)

  obtain ⟨c₀, h₀₁, h₀₂⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h n o o ζ ζ (RingHom.id o) F.X F.X (F.s ≫ spMap (RingHom.id o)) F.s (𝟙 _) rfl
    (by simp)).2.2 F.univ
  have r₀₁ : SRel F.univ c₀ 1 1 (𝟙 _) := (sRel_one_one_iff _ _ _).2 h₀₁
  have r₀₂ : SRel c₀ F.univ 1 1 (𝟙 _) := (sRel_one_one_iff _ _ _).2 h₀₂
  have p₀ : c₀.Principal := sRel_principal r₀₂ F.princ
  obtain ⟨S₁, π, C, hfin, het, hsurj, hlow, huniv⟩ :=
    GlobalTheory.T.exists_finite_etale_deeper_level_siegel_cover h n N o o ζ b (RingHom.id o) F.X F.s c₀ hn hN hnN rfl p₀
  have hN0 : N ≠ 0 := hN.pos.ne'
  have pC : C.Principal := sRel_principal hlow p₀
  refine ⟨{
    X := S₁
    s := π ≫ F.s
    smooth := by
      haveI := F.smooth
      have := smoothOfRelativeDimension_comp 0 (h * (h + 1) / 2) π F.s
      rwa [zero_add] at this
    qproj := GlobalTheory.T.isQProjOver_comp_of_isFinite_noetherianBase o _ _ π F.s hfin F.qproj
    univ := C
    princ := pC
    rep := ?_
    inj := ?_ }⟩
  · intro T s' c hred hdense hp
    obtain ⟨cl, hcl1, hcl2⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N o o ζ (b.ζ : o) (RingHom.id o) T s' c hN0 b.unit hnN rfl
    have pl : cl.Principal := sRel_principal hcl2 hp
    obtain ⟨f, hf, hfp⟩ := F.rep T (s' ≫ spMap (RingHom.id o)) cl hred
      (by rw [spMap_id_eq, Category.comp_id]; exact hdense) pl
    rw [spMap_id_eq, Category.comp_id] at hf
    subst hf
    have r1 : SRel c F.univ (N / n) 1 (𝟙 _ ≫ f) := sRel_trans ((sRel_one_one_iff _ _ _).2 hfp) hcl1
    have r2 : SRel c c₀ (N / n) 1 ((𝟙 _ ≫ f) ≫ 𝟙 _) := sRel_trans r₀₁ r1
    obtain ⟨t₁, ⟨ht₁, hC⟩, -⟩ := huniv T f c (by simpa using r2)
    exact ⟨t₁, by rw [← Category.assoc, ht₁], hC⟩
  · intro R _ _ x y s' c hxy hx hy
    have rx : SRel c C 1 1 x := (sRel_one_one_iff _ _ _).2 hx
    have ry : SRel c C 1 1 y := (sRel_one_one_iff _ _ _).2 hy
    have kx : SRel c c₀ (N / n) 1 (x ≫ π) := sRel_trans hlow (by simpa using sRel_scale rx (N / n))
    have ky : SRel c c₀ (N / n) 1 (y ≫ π) := sRel_trans hlow (by simpa using sRel_scale ry (N / n))

    obtain ⟨cx, hcx⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h n o o ζ ζ (RingHom.id o) F.X (Sp R) (F.s ≫ spMap (RingHom.id o))
      ((x ≫ π) ≫ F.s) (x ≫ π) rfl (by simp)).1 c₀
    have e1 : SRel cx c₀ 1 1 (x ≫ π) := (sRel_one_one_iff _ _ _).2 hcx
    have e2 : SRel cx c 1 (N / n) (𝟙 _) := sRel_cancel (f' := 𝟙 _) kx (by simpa using e1)
    have e3 : SRel cx c₀ 1 1 (𝟙 _ ≫ y ≫ π) := sRel_trans ky e2
    have fx : SiegPB cx F.univ (x ≫ π) := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans r₀₂ e1)
    have fy : SiegPB cx F.univ (y ≫ π) := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans r₀₂ e3)
    have hπ : x ≫ π = y ≫ π := F.inj R (x ≫ π) (y ≫ π) _ cx (by simpa using hxy) fx fy

    obtain ⟨Cx, hCx⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h N o o (b.ζ : o) (b.ζ : o) (RingHom.id o) S₁ (Sp R) (π ≫ F.s)
      ((x ≫ π) ≫ F.s) x rfl (by rw [spMap_id_eq]; simp)).1 C
    have g1 : SRel Cx C 1 1 x := (sRel_one_one_iff _ _ _).2 hCx
    have g2 : SRel Cx c₀ (N / n) 1 (x ≫ π) := sRel_trans hlow (by simpa using sRel_scale g1 (N / n))
    have g3 : SRel Cx c 1 1 (𝟙 _) := sRel_cancel (f' := 𝟙 _) rx (by simpa using g1)
    have g4 : SiegPB Cx C y := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans ry g3)
    exact (huniv (Sp R) (x ≫ π) Cx g2).unique ⟨rfl, hCx⟩ ⟨hπ.symm, g4⟩

end GlobalTheory.SiegLev
