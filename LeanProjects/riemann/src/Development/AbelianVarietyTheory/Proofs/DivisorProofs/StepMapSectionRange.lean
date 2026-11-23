import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecSecCol

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagZ
  GlobalTheory.FlagZ.TautUniq

namespace GlobalTheory.FlagZ.TautUniq

theorem isFrame_pullStd {N : ℕ} {A : Type} [CommRing A] (y : Sp A ⟶ Sp ℤ) :
    IsFrame (F := (Scheme.Modules.pullback y).obj (Taut.stdE N)) (U := ⊤) fun i : Fin N =>
      QCoh.pullbackSections y (Taut.stdE N) (by simp) (freeFrame (Sp ℤ) (Fin N) i) := by
  haveI := (isVB_freeModule (Sp ℤ) (Fin N)).isQuasicoherent
  have h := ((isFrame_freeFrame (Sp ℤ) (Fin N)).pullback y).res (V := ⊤) (by simp)
  have e : (fun i : Fin N => QCoh.pullbackSections y (Taut.stdE N) (by simp) (freeFrame (Sp ℤ) (Fin N) i)) =
      fun i => Twist.resM _ (by simp : (⊤ : (Sp A).Opens) ≤ y ⁻¹ᵁ ⊤)
        (QCoh.pullbackSections y (QCoh.freeModule (Sp ℤ) (Fin N)) le_rfl (freeFrame (Sp ℤ) (Fin N) i)) :=
    funext fun i => (QCoh.res_pullbackSections _ _ _ _ _).symm
  rw [e]
  exact h

theorem vecSec_injective {N : ℕ} {A : Type} [CommRing A] (y : Sp A ⟶ Sp ℤ) :
    Function.Injective (vecSec (N := N) y) := by
  intro v w hvw
  have hinj := (isFrame_pullStd (N := N) y ⊤ le_rfl).1
  simp only [Twist.resM_self] at hinj
  have := hinj (a₁ := fun i => (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (v i))
    (a₂ := fun i => (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (w i))
    (by simpa only [Fintype.linearCombination_apply, vecSec] using hvw)
  funext i
  have hi := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (congrFun this i)
  simpa using hi

theorem vecSec_sum_smul {N : ℕ} {A : Type} [CommRing A] (y : Sp A ⟶ Sp ℤ) {κ : Type} [Fintype κ]
    (a : κ → A) (c : κ → Fin N → A) :
    vecSec y (∑ j, a j • c j) = ∑ j, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (a j) • vecSec y (c j) := by
  simp only [vecSec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_smul, mul_smul,
    Finset.smul_sum]
  exact Finset.sum_comm

theorem mem_range_app_iff {X : Scheme.{0}} {F G : X.Modules} {κ : Type} [Fintype κ] {s : κ → Γ(F, ⊤)}
    (hs : IsFrame s) (ψ : F ⟶ G) (x : Γ(G, ⊤)) :
    x ∈ Set.range (ψ.app ⊤) ↔ ∃ r : κ → Γ(X, ⊤), ∑ j, r j • ψ.app ⊤ (s j) = x := by
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨r, hr⟩ := (hs ⊤ le_rfl).2 t
    refine ⟨r, ?_⟩
    rw [← hr]
    simp only [Fintype.linearCombination_apply, Twist.resM_self, ← QCoh.homAppLinear_apply, map_sum, map_smul]
  · rintro ⟨r, rfl⟩
    exact ⟨∑ j, r j • s j, by simp only [← QCoh.homAppLinear_apply, map_sum, map_smul]⟩

theorem vecSec_mem_range_stepMap_iff : ∀ (ι : Type) [Fintype ι] (N : ℕ)
    (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N), Taut.IsTaut ι N fl →
    ∀ (A : Type) [CommRing A] (h : ι → GL (Fin N) A) (y : Sp A ⟶ Sp ℤ)
      (hy : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd h ≫ flStr ι N = y) (a : ι) (l : Fin (N + 1))
      (v : Fin N → A),
    vecSec y v ∈ Set.range ((stepMap ι N fl (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd h) y hy a l).app ⊤) ↔
      v ∈ Submodule.span A (Set.range fun j : Fin l => fun i => (h a).1 i (Fin.castLE l.is_le j)) := by
  intro ι _ N fl hfl A _ h y hy a l v
  subst hy
  obtain ⟨s, hs, hsj⟩ := hfl A h a l
  have hstep : stepMap ι N fl (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd h) _ rfl a l =
      (Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd h)).map ((fl a).ι l) ≫
        (Scheme.Modules.pullbackComp (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd h) (flStr ι N)).hom.app
          (Taut.stdE N) := by
    simp [stepMap, Scheme.Modules.pullbackCongr]
  rw [hstep, mem_range_app_iff hs, Submodule.mem_span_range_iff_exists_fun]
  simp only [hsj, ← vecSec_col]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨fun j => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (r j), vecSec_injective (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd h ≫ flStr ι N) ?_⟩
    rw [vecSec_sum_smul, ← hr]
    simp
  · rintro ⟨c, rfl⟩
    exact ⟨fun j => (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (c j), (vecSec_sum_smul _ _ _).symm⟩

end GlobalTheory.FlagZ.TautUniq
