import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthOfAvTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCongruenceConjContainsCongruence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAdmissibleUnitaryMemSupIsotypicParts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPeterssonStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWtExistsInvFormStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CompRed

open GlobalTheory.CoefDuty

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GQ L n) W}

theorem indep_of_orth {M : Type} [AddCommGroup M] [Module ℂ M] (B : M → M →ₗ[ℂ] ℂ) {ι : Type*}
    (t : ι → Submodule ℂ M) (hpos : ∀ i, ∀ x ∈ t i, B x x = 0 → x = 0)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ t i, ∀ y ∈ t j, B x y = 0) : iSupIndep t := by
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx1, hx2⟩
  have hle : (⨆ (j) (_ : j ≠ i), t j) ≤ LinearMap.ker (B x) :=
    iSup₂_le fun j hj y hy => horth i j (Ne.symm hj) x hx1 y hy
  exact (Submodule.mem_bot ℂ).2 (hpos i x hx1 (hle hx2))

theorem isoRep_refl (S : Submodule ℂ (GAf L n → W)) : NG.IsoRep S S :=
  ⟨LinearEquiv.refl ℂ S, fun _ _ _ e => by simpa using e⟩

theorem isoTyp_le (S : Submodule ℂ (GAf L n → W)) : NG.isoTyp ρ S ≤ NG.AFall L n ρ :=
  sSup_le fun _ hU => hU.1.1.le

theorem isoTyp_stable (S : Submodule ℂ (GAf L n → W)) (h : GAf L n) :
    ∀ f ∈ NG.isoTyp ρ S, NG.rt L n h f ∈ NG.isoTyp ρ S := by
  intro f hf
  have : NG.isoTyp ρ S ≤ (NG.isoTyp ρ S).comap (NG.rt L n h) :=
    sSup_le fun U hU g hg => (le_sSup hU : U ≤ NG.isoTyp ρ S) (hU.1.1.stable h g hg)
  exact this hf

theorem isoTyp_subrep (S : Submodule ℂ (GAf L n → W)) : NG.IsSubrep ρ (NG.isoTyp ρ S) :=
  ⟨isoTyp_le S, fun h f hf => isoTyp_stable S h f hf⟩

theorem le_isoTyp {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S) : S ≤ NG.isoTyp ρ S :=
  le_sSup ⟨hS, isoRep_refl S⟩

theorem isoTyp_eq {S S' : Submodule ℂ (GAf L n → W)} (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S)
    (h : NG.IsoRep S S') : NG.isoTyp ρ S = NG.isoTyp ρ S' := by
  unfold NG.isoTyp
  congr 1
  ext T
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (h.symm hS).trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h.trans h2⟩⟩

variable {B : (GAf L n → W) →ₗ⋆[ℂ] (GAf L n → W) →ₗ[ℂ] ℂ}

theorem pos_zero (hB : GlobalTheory.TypeOrthogonality.Good ρ B) {x : GAf L n → W} (hx : x ∈ NG.AFall L n ρ) (h0 : B x x = 0) :
    x = 0 := by
  by_contra hne
  have := (hB x hx x hx).2.1 hne
  rw [h0] at this
  simp at this

theorem isoTyp_orth (hB : GlobalTheory.TypeOrthogonality.Good ρ B) (hfin : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ NG.AFall L n ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g}))
    {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S) (hS' : NG.IsIrrRep ρ S')
    (hne : ¬ NG.IsoRep S S') : ∀ x ∈ NG.isoTyp ρ S, ∀ y ∈ NG.isoTyp ρ S', B x y = 0 := by
  intro x hx y hy
  have step : ∀ U, NG.IsIrrRep ρ U → NG.IsoRep S U → ∀ a ∈ U, ∀ b ∈ NG.isoTyp ρ S', B a b = 0 := by
    intro U hU h1 a ha b hb
    have hle : NG.isoTyp ρ S' ≤ LinearMap.ker (B a) := by
      refine sSup_le fun U' hU' => ?_
      intro c hc
      exact GlobalTheory.TypeOrthogonality.orth_of_not_iso hB hfin hU hU'.1
        (fun h3 => hne ((h1.trans h3).trans (hU'.2.symm hS'.1.stable))) a ha c hc
    exact hle hb
  have hle : NG.isoTyp ρ S ≤ LinearMap.ker (B.flip y) := by
    refine sSup_le fun U hU => ?_
    intro a ha
    exact step U hU.1 hU.2 a ha _ hy
  exact hle hx

theorem proj_typeSp (hB : GlobalTheory.TypeOrthogonality.Good ρ B) {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {U : Submodule ℂ (GAf L n → W)} (hU : NG.IsSubrep ρ U) {x p : GAf L n → W} (hx : x ∈ NG.TypeSp ρ J χ)
    (hp : p ∈ U) (hxp : ∀ w ∈ U, B (x - p) w = 0) : p ∈ NG.TypeSp ρ J χ := by
  refine ⟨hU.le hp, fun κ => ?_⟩
  set c : ℂ := ((χ κ : ℂˣ) : ℂ)
  have hxc : NG.rt L n (κ : GAf L n) x = c • x := hx.2 κ
  have hxA : x - p ∈ NG.AFall L n ρ := (NG.AFall L n ρ).sub_mem hx.1 (hU.le hp)
  refine GlobalTheory.TypeOrthogonality.proj_unique hB hU.le (hU.stable _ p hp) (U.smul_mem c hp) (u := NG.rt L n (κ : GAf L n) x)
    (fun w hw => ?_) (fun w hw => ?_)
  · have hw' : NG.rt L n (κ : GAf L n)⁻¹ w ∈ U := hU.stable _ w hw
    rw [← map_sub, ← GlobalTheory.TypeOrthogonality.rt_rt_inv (κ : GAf L n) w, (hB _ hxA _ (hU.le hw')).2.2]
    exact hxp _ hw'
  · rw [hxc, ← smul_sub, map_smulₛₗ, LinearMap.smul_apply, hxp w hw, smul_zero]

end Gen

theorem rt_mem_AFall {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GQ L n) W} (h : GAf L n) {f : GAf L n → W} (hf : f ∈ NG.AFall L n ρ) :
    NG.rt L n h f ∈ NG.AFall L n ρ := by
  obtain ⟨h1, N, hN, h2⟩ := hf
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h N hN
  refine ⟨fun γ g => ?_, N', hN', fun κ hκ g => ?_⟩
  · show f ((γ : GAf L n) * g * h) = ρ γ (f (g * h))
    rw [mul_assoc]; exact h1 γ _
  · show f (g * κ * h) = f (g * h)
    have := h2 _ (hc κ hκ) (g * h)
    rw [← this]; congr 1; group

def rtHom (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] :
    GAf L n →* Module.End ℂ (GAf L n → W) where
  toFun h := NG.rt L n h
  map_one' := by ext f g; simp [NG.rt]
  map_mul' a b := by ext f g; simp [NG.rt, mul_assoc]

theorem mem_sSup_irrRep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (B : (GAf L n → a.W) →ₗ⋆[ℂ] (GAf L n → a.W) →ₗ[ℂ] ℂ), GlobalTheory.CoefDuty.IsPetersson a B → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ NG.AFall L n a.ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g})) → ∀ x ∈ NG.AFall L n a.ρ, x ∈ sSup {S | NG.IsIrrRep a.ρ S} := by
  intro L _ _ _ n a B hB hfin x hx
  classical
  have hG : GlobalTheory.TypeOrthogonality.Good a.ρ B := hB
  set C := NG.AFall L n a.ρ with hCdef
  let ρ := rtHom L n a.W
  have hρ : ∀ h f, ρ h f = NG.rt L n h f := fun _ _ => rfl
  have h1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z := by
    intro x _ y _ z _ c; simp
  have h2 : ∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x) := fun x hx y hy => (hG x hx y hy).1
  have h3 : ∀ x ∈ C, x ≠ 0 → 0 < (B x x).re := fun x hx h => (hG x hx x hx).2.1 h
  have h4 : ∀ h, ∀ x ∈ C, ρ h x ∈ C := fun h x hx => rt_mem_AFall h hx
  obtain ⟨N, hN, hxN⟩ := hx.2
  let core := GlobalTheory.IsotOrth.coreOf C (fun x y => B x y) h1 h2 h3
  letI : NormedAddCommGroup C := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ C := InnerProductSpace.ofCore core.toCore
  let ρC := GlobalTheory.IsotOrth.rhoC ρ C h4
  have hρC : ∀ g (c : C), ((ρC g c : C) : GAf L n → a.W) = NG.rt L n g c := fun g c => rfl
  have hunit : ∀ g (x y : C), inner ℂ (ρC g x) (ρC g y) = inner ℂ x y :=
    fun g x y => (hG x x.2 y y.2).2.2 g
  let F : Submodule ℂ C :=
    { carrier := {v | ∀ k ∈ GlobalTheory.IsotOrth.congSub L n N, ρC k v = v}
      zero_mem' := fun k _ => map_zero _
      add_mem' := fun ha hb k hk => by rw [map_add, ha k hk, hb k hk]
      smul_mem' := fun c v hv k hk => by rw [map_smul, hv k hk] }
  haveI := hfin N hN
  let ι : F →ₗ[ℂ] ↥(Submodule.span ℂ {f | f ∈ NG.AFall L n a.ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g}) :=
    (C.subtype.comp F.subtype).codRestrict _ (fun w => Submodule.subset_span ⟨w.1.2, fun κ hκ g => by
      have := congrArg Subtype.val (w.2 κ hκ)
      exact congrFun this g⟩)
  have hι : Function.Injective ι := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  haveI : FiniteDimensional ℂ F := FiniteDimensional.of_injective ι hι
  have hF : ∀ v, v ∈ F ↔ ∀ k ∈ GlobalTheory.IsotOrth.congSub L n N, ρC k v = v := fun v => Iff.rfl
  have horb : ∀ y : C, ((fun k => ρC k y) '' (GlobalTheory.IsotOrth.congSub L n N : Set (GAf L n))).Finite := by
    intro y
    obtain ⟨N', hN', hy⟩ := y.2.2
    refine (GlobalTheory.IsotOrth.orbit_finite ρC hN' y (fun κ hκ => Subtype.ext (funext fun g => hy κ hκ g))).subset ?_
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hk.1, rfl⟩
  have hmem := GlobalTheory.SpanIsot.mem_sSup_irr ρC hunit _ F hF horb ⟨x, hx⟩
    (fun κ hκ => Subtype.ext (funext fun g => hxN κ hκ g))
  have hle : sSup {W | GlobalTheory.SpanIsot.IrrSub ρC W} ≤ (sSup {S | NG.IsIrrRep a.ρ S}).comap C.subtype := by
    refine sSup_le fun W hW => ?_
    rw [← Submodule.map_le_iff_le_comap]
    obtain ⟨hW0, hWs, hWi⟩ := hW
    refine le_sSup ⟨⟨Submodule.map_subtype_le _ _, ?_⟩, ?_, ?_⟩
    · rintro h _ ⟨w, hw, rfl⟩
      exact ⟨ρC h w, hWs h w hw, rfl⟩
    · intro h
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      have : ((w : C) : GAf L n → a.W) ∈ W.map C.subtype := ⟨w, hw, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hw0 (Subtype.ext this)
    · intro W' hW' hW'W
      have hs : GlobalTheory.SpanIsot.Stab ρC (W'.comap C.subtype) := fun g c hc => by
        show ((ρC g c : C) : GAf L n → a.W) ∈ W'
        rw [hρC]
        exact hW'.stable g _ hc
      have hle' : W'.comap C.subtype ≤ W := by
        intro c hc
        obtain ⟨w, hw, e⟩ := hW'W hc
        have : w = c := Subtype.ext e
        rw [← this]
        exact hw
      rcases hWi _ hle' hs with h | h
      · left
        rw [eq_bot_iff]
        intro a ha
        obtain ⟨w, _, rfl⟩ := hW'W ha
        have : w ∈ W'.comap C.subtype := ha
        rw [h, Submodule.mem_bot] at this
        rw [Submodule.mem_bot, this]
        rfl
      · right
        refine le_antisymm hW'W ?_
        rintro _ ⟨w, hw, rfl⟩
        have : w ∈ W'.comap C.subtype := by rw [h]; exact hw
        exact this
  exact hle hmem

theorem typeSp_decomp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → FiniteDimensional ℂ (NG.TypeSp a.ρ J χ) ∧ ∃ (ι : Type) (_ : Finite ι) (S : ι → Submodule ℂ (GAf L n → a.W)), (∀ i, NG.IsIrrRep a.ρ (S i)) ∧ (∀ i i', NG.IsoRep (S i) (S i') → i = i') ∧ (∀ S', NG.IsIrrRep a.ρ S' → NG.isoTyp a.ρ S' ⊓ NG.TypeSp a.ρ J χ ≠ ⊥ → ∃ i, NG.IsoRep (S i) S') ∧ (∀ i, NG.isoTyp a.ρ (S i) ⊓ NG.TypeSp a.ρ J χ ≠ ⊥) ∧ iSupIndep (fun i => NG.isoTyp a.ρ (S i)) ∧ ⨆ i, NG.isoTyp a.ρ (S i) ⊓ NG.TypeSp a.ρ J χ = NG.TypeSp a.ρ J χ := by
  intro L _ _ _ n a J χ hlev
  classical
  obtain ⟨N, hN, hNJ⟩ := hlev
  haveI hW : FiniteDimensional ℂ a.W := a.alg.1
  have hT := GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n
  have hfin : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ NG.AFall L n a.ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g}) := by
    intro M hM
    haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n a.ρ hT hM
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n a.ρ M) (Submodule.span_le.2 ?_)
    rintro f ⟨hf, hκ⟩
    exact ⟨hf.1, hκ⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.T.algWt_exists_invForm' L n a
  obtain ⟨B, hB, -⟩ := GlobalTheory.T.class_sum_eq_const_mul_petersson L n a β hβ
  have hG : GlobalTheory.TypeOrthogonality.Good a.ρ B := hB
  set V := NG.TypeSp a.ρ J χ with hVdef
  have hVA : V ≤ NG.AFall L n a.ρ := fun f hf => hf.1
  have hVle : V ≤ Submodule.span ℂ {f | f ∈ NG.AFall L n a.ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g} := by
    intro f hf
    refine Submodule.subset_span ⟨hf.1, fun κ hκ g => ?_⟩
    obtain ⟨hJ, h1⟩ := hNJ κ hκ
    have := congrFun (hf.2 ⟨κ, hJ⟩) g
    rw [h1] at this
    simpa [NG.rt] using this
  haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ NG.AFall L n a.ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g}) := hfin N hN
  haveI hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVle
  refine ⟨hVfd, ?_⟩

  let P : Set (Submodule ℂ (GAf L n → a.W)) := {q | q ≠ ⊥ ∧ ∃ S, NG.IsIrrRep a.ρ S ∧ q = NG.isoTyp a.ρ S ⊓ V}
  have hPorth : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' → ∀ x ∈ q, ∀ y ∈ q', B x y = 0 := by
    rintro q ⟨-, S, hS, rfl⟩ q' ⟨-, S', hS', rfl⟩ hne x hx y hy
    by_cases hi : NG.IsoRep S S'
    · exact absurd (by rw [isoTyp_eq hS.1.stable hi]) hne
    · exact isoTyp_orth hG hfin hS hS' hi x hx.1 y hy.1
  have hPfin : Finite P := by
    let t : P → Submodule ℂ V := fun q => (q : Submodule ℂ (GAf L n → a.W)).comap V.subtype
    have hind : iSupIndep t := by
      refine indep_of_orth (fun x : V => (B x).comp V.subtype) t (fun i x _ h0 => ?_) (fun i j hij x hx y hy => ?_)
      · exact Subtype.ext (pos_zero hG (hVA x.2) h0)
      · exact hPorth i i.2 j j.2 (fun e => hij (Subtype.ext e)) x hx y hy
    have hf := Submodule.finite_ne_bot_of_iSupIndep hind
    have hall : ∀ q : P, t q ≠ ⊥ := by
      rintro ⟨q, hq0, S, hS, rfl⟩ h
      apply hq0
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : V) ∈ t ⟨_, hq0, S, hS, rfl⟩ := hx
      rw [h, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val this)
    have : (Set.univ : Set P).Finite := hf.subset fun q _ => hall q
    exact Set.finite_univ_iff.1 this
  have hPspec : ∀ q : P, ∃ S, NG.IsIrrRep a.ρ S ∧ (q : Submodule ℂ (GAf L n → a.W)) = NG.isoTyp a.ρ S ⊓ V :=
    fun q => q.2.2
  choose S hSirr hSq using hPspec
  have hinj : ∀ i i' : P, NG.IsoRep (S i) (S i') → i = i' := by
    intro i i' h
    apply Subtype.ext
    rw [hSq i, hSq i', isoTyp_eq (hSirr i).1.stable h]
  have hcover : ∀ S', NG.IsIrrRep a.ρ S' → NG.isoTyp a.ρ S' ⊓ V ≠ ⊥ → ∃ i, NG.IsoRep (S i) S' := by
    intro S' hS' hne
    let i : P := ⟨_, hne, S', hS', rfl⟩
    refine ⟨i, ?_⟩
    by_contra hni
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hxi : x ∈ (i : Submodule ℂ (GAf L n → a.W)) := hx
    rw [hSq i] at hxi
    exact hx0 (pos_zero hG (hVA hx.2) (isoTyp_orth hG hfin (hSirr i) hS' hni x hxi.1 x hx.1))
  have hne : ∀ i : P, NG.isoTyp a.ρ (S i) ⊓ V ≠ ⊥ := fun i => by rw [← hSq i]; exact i.2.1
  have horth : ∀ i j : P, i ≠ j → ∀ x ∈ NG.isoTyp a.ρ (S i), ∀ y ∈ NG.isoTyp a.ρ (S j), B x y = 0 :=
    fun i j hij => isoTyp_orth hG hfin (hSirr i) (hSirr j) (fun h => hij (hinj i j h))
  have hindep : iSupIndep fun i : P => NG.isoTyp a.ρ (S i) :=
    indep_of_orth (fun x => B x) _ (fun i x hx h0 => pos_zero hG (isoTyp_le _ hx) h0) horth
  refine ⟨P, hPfin, S, hSirr, hinj, hcover, hne, hindep, ?_⟩
  haveI : Fintype P := Fintype.ofFinite P
  refine le_antisymm (iSup_le fun i => inf_le_right) fun x hx => ?_
  have hxA : x ∈ NG.AFall L n a.ρ := hx.1
  have hproj : ∀ i : P, ∃ p ∈ NG.isoTyp a.ρ (S i), ∀ w ∈ NG.isoTyp a.ρ (S i), B (x - p) w = 0 :=
    fun i => GlobalTheory.TypeOrthogonality.proj_all hG hfin (isoTyp_subrep (S i)) x hxA
  choose p hpmem hpo using hproj
  have hpV : ∀ i, p i ∈ V := fun i => proj_typeSp hG (isoTyp_subrep (S i)) hx (hpmem i) (hpo i)
  have hsum : ∑ i, p i ∈ ⨆ i : P, NG.isoTyp a.ρ (S i) ⊓ V :=
    Submodule.sum_mem _ fun i _ => (le_iSup (fun i : P => NG.isoTyp a.ρ (S i) ⊓ V) i) ⟨hpmem i, hpV i⟩
  set y := x - ∑ i, p i with hy
  have hyV : y ∈ V := V.sub_mem hx (V.sum_mem fun i _ => hpV i)
  have hyA : y ∈ NG.AFall L n a.ρ := hVA hyV
  have hy1 : ∀ i : P, ∀ w ∈ NG.isoTyp a.ρ (S i), B y w = 0 := by
    intro i w hw
    have e : B y w = B (x - p i) w - ∑ j ∈ Finset.univ.erase i, B (p j) w := by
      simp only [hy, map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      ring
    rw [e, hpo i w hw, Finset.sum_eq_zero fun j hj => horth j i (Finset.ne_of_mem_erase hj) _ (hpmem j) w hw,
      sub_zero]
  have hy2 : ∀ U, NG.IsIrrRep a.ρ U → ∀ w ∈ U, B y w = 0 := by
    intro U hU w hw
    obtain ⟨q, hq, hqo⟩ := GlobalTheory.TypeOrthogonality.proj_all hG hfin (isoTyp_subrep U) y hyA
    have hqV : q ∈ V := proj_typeSp hG (isoTyp_subrep U) hyV hq hqo
    by_cases hq0 : q = 0
    · have := hqo w (le_isoTyp hU hw)
      rwa [hq0, sub_zero] at this
    · have hne' : NG.isoTyp a.ρ U ⊓ V ≠ ⊥ := fun h => hq0 (by
        have : q ∈ NG.isoTyp a.ρ U ⊓ V := ⟨hq, hqV⟩
        rwa [h, Submodule.mem_bot] at this)
      obtain ⟨i, hi⟩ := hcover U hU hne'
      refine hy1 i w ?_
      rw [isoTyp_eq (hSirr i).1.stable hi]
      exact le_isoTyp hU hw
  have hyS := mem_sSup_irrRep L n a B hB hfin y hyA
  have hle : sSup {S | NG.IsIrrRep a.ρ S} ≤ LinearMap.ker (B y) := sSup_le fun U hU w hw => hy2 U hU w hw
  have hy0 : y = 0 := pos_zero hG hyA (hle hyS)
  have : x = ∑ i, p i := by rw [← sub_eq_zero]; exact hy0
  rw [this]
  exact hsum

end GlobalTheory.CompRed
