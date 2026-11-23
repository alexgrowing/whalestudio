import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exSec {W P : Type} {X : P → Type} (f : W → P) (S : Set W) (inj : Set.InjOn f S)
    (g : ∀ w, w ∈ S → X (f w)) (d : ∀ p, X p) : ∃ b : ∀ p, X p, ∀ w (h : w ∈ S), b (f w) = g w h := by
  classical
  refine ⟨fun p => if h : ∃ w, ∃ hw : w ∈ S, f w = p then h.choose_spec.choose_spec ▸ g _ h.choose_spec.choose else d p, ?_⟩
  intro w hw
  have key : ∀ (w' : W) (hw' : w' ∈ S) (he : f w' = f w), (he ▸ g w' hw' : X (f w)) = g w hw := by
    intro w' hw' he
    obtain rfl := inj hw' hw he
    rfl
  have hex : ∃ w', ∃ hw' : w' ∈ S, f w' = f w := ⟨w, hw, rfl⟩
  simp only [dif_pos hex]
  exact key _ _ _

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem exOver (v : Pl (Lp L)) : ∃ w : Plc L, un w = v := by
  haveI := v.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hne : P ≠ ⊥ := fun h => v.ne_bot (by
    rw [hP.over, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 (Lp L)) (𝓞 L)))
  exact ⟨⟨P, hPm.isPrime, hne⟩, HeightOneSpectrum.ext (by
    rw [HeightOneSpectrum.under_asIdeal]
    exact hP.over.symm)⟩

private theorem exTwo : ∃ w : Plc L, (2 : 𝓞 L) ∈ w.asIdeal := by
  have hu : ¬ IsUnit (2 : 𝓞 L) := fun h => by
    obtain ⟨u, hu⟩ := h.exists_right_inv
    have e : ((u : 𝓞 L) : L) = algebraMap ℚ L (1 / 2) := by
      have e1 : (2 : L) * ((u : 𝓞 L) : L) = 1 := by
        have := congrArg (algebraMap (𝓞 L) L) hu
        rwa [map_mul, map_ofNat, map_one] at this
      rw [map_div₀, map_one, map_ofNat]
      field_simp
      linear_combination e1
    have hi : IsIntegral ℤ (algebraMap ℚ L (1 / 2)) := e ▸ u.2
    have hi' : IsIntegral ℤ (1 / 2 : ℚ) := (isIntegral_algebraMap_iff (algebraMap ℚ L).injective).1 hi
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi'
    have h2 : (2 : ℚ) * (y : ℚ) = 1 := by
      rw [show (y : ℚ) = 1 / 2 from hy]; norm_num
    have h3 : (2 : ℤ) * y = 1 := by exact_mod_cast h2
    omega
  obtain ⟨P, hPm, hP⟩ := exists_max_ideal_of_mem_nonunits hu
  have hne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hP
    exact two_ne_zero hP
  exact ⟨⟨P, hPm.isPrime, hne⟩, hP⟩

private theorem two_under (w : Plc L) (h : (2 : 𝓞 (Lp L)) ∈ (un w).asIdeal) : (2 : 𝓞 L) ∈ w.asIdeal := by
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_ofNat] at h
  exact h

private def pullLev {B : Bridge L} {w : Plc L} (T : B.toRingBr.Split w) (V : Lev (Kw w)) : Lev (Kv (un w)) where
  c := V.c
  H := V.H.comap (Units.map (T.i : Kv (un w) →* Kw w))
  le := fun x hx => V.le ((T.Uc _ x).2 hx)
  H_le := fun x hx => (T.Uo x).1 (V.H_le hx)

theorem UpperTheory.V.Z.Sym.So.fitEx :
    UpperTheory.V.Z.Sym.So.FitEx := by
  classical
  intro L _ _ _ B hB T S VL hP h2
  have hinj : Set.InjOn (fun w : Plc L => un w) (S : Set (Plc L)) := hP.inj
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨sf, hsf⟩ := exSec (X := fun v : Pl (Lp L) => Kv v) (fun w : Plc L => un w) (S : Set (Plc L)) hinj
      (fun w hw => (T w (hP.split w hw)).s) (fun _ => 0)
    obtain ⟨Vf, hVf⟩ := exSec (X := fun v : Pl (Lp L) => Lev (Kv v)) (fun w : Plc L => un w) (S : Set (Plc L)) hinj
      (fun w hw => pullLev (T w (hP.split w hw)) (VL w)) (fun _ => Lev.iw _)
    obtain ⟨χ, hχ⟩ := hB.chi
    have hs : ∀ v ∈ S.image (fun w : Plc L => un w), sf v * sf v = cv v B.Δ := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
      rw [hsf w hw]
      exact (T w (hP.split w hw)).hs
    let A : SD B.Δ :=
      { Sg := S.image (fun w : Plc L => un w)
        s := sf
        hs := hs
        V := Vf
        Ry := fun v => (finFacts _ (Vf v)).2.2.2.2.1.choose
        χ := χ }
    have hoff : ∀ v ∉ A.Sg, (2 : 𝓞 (Lp L)) ∉ v.asIdeal := by
      intro v hv h
      obtain ⟨w, rfl⟩ := exOver v
      obtain ⟨w', hw', he⟩ := h2 w (two_under w h)
      exact hv (Finset.mem_image.2 ⟨w', hw', he⟩)
    refine ⟨A, ⟨inferInstance, B.neg, ?_, ?_, ?_, ?_⟩, ⟨hP, ?_, ?_, ?_, ?_⟩⟩
    · obtain ⟨w, hw⟩ := exTwo (L := L)
      obtain ⟨w', hw', -⟩ := h2 w hw
      exact ⟨_, Finset.mem_image_of_mem _ hw'⟩
    · exact fun v hv => B.loc v (hoff v hv)
    · intro v
      by_cases hv : v ∈ A.Sg
      · exact hχ v (Or.inr ⟨sf v, (hs v hv).symm⟩)
      · exact hχ v (Or.inl (hoff v hv))
    · exact fun v _ => (finFacts _ (Vf v)).2.2.2.2.1.choose_spec
    · intro v
      simp [A]
    · intro w hw h
      exact hsf w hw
    · intro w hw
      show (Vf (un w)).c = _
      rw [hVf w hw]; rfl
    · intro w hw h x
      show _ ↔ x ∈ (Vf (un w)).H
      rw [hVf w hw]; rfl
  · obtain ⟨b, hb⟩ := exSec (X := fun v : Pl (Lp L) => (Kv v)ˣ →* ℂˣ) (fun w : Plc L => un w) (S : Set (Plc L)) hinj
      (fun w hw => (a w).comp (iu T w (hP.split w hw))) (fun _ => 1)
    exact ⟨b, fun w hw h => hb w hw⟩

end
