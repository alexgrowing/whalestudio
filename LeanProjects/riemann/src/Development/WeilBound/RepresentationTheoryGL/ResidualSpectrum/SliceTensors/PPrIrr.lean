import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAdm
import GroundTheory.PAdicHodge.NormalizedTrace

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CapOrth
  GlobalTheory.LevelTypeProj GlobalTheory.PRep GlobalTheory.CuspRep.LocEx PositivityTheory.Rg.Rs.PrAdm

namespace PositivityTheory.Rg.Rs.PrIrr

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem isStable_sInf (S : Set (Submodule ℂ (Sm E N))) (hS : ∀ U ∈ S, IsStable U) : IsStable (sInf S) := by
  intro o φ hφ
  rw [Submodule.mem_sInf] at hφ ⊢
  exact fun U hU => hS U hU o φ (hφ U hU)

variable {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
  (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)

def orthIn (V U : Submodule ℂ (Sm E N)) (hV : V ≤ W) : Submodule ℂ (Sm E N) where
  carrier := {x | x ∈ V ∧ ∀ u ∈ U, inner ℂ (cls h x) (cls h u) = 0}
  add_mem' := fun {x y} hx hy => ⟨V.add_mem hx.1 hy.1, fun u hu => by
    rw [cls_add h (hV hx.1) (hV hy.1), inner_add_left, hx.2 u hu, hy.2 u hu, add_zero]⟩
  zero_mem' := ⟨V.zero_mem, fun u _ => by
    rw [show (0 : Sm E N) = (0 : ℂ) • (0 : Sm E N) by simp, cls_smul h 0 W.zero_mem, zero_smul, inner_zero_left]⟩
  smul_mem' := fun c x hx => ⟨V.smul_mem c hx.1, fun u hu => by
    rw [cls_smul h c (hV hx.1), inner_smul_left, hx.2 u hu, mul_zero]⟩

theorem exists_irr (hW : IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (hinj : ∀ x ∈ W, cls h x = 0 → x = 0)
    (hadj : ∀ o : Op E N, ∃ B : Module.End ℂ (Sm E N), (∀ U : Submodule ℂ (Sm E N), IsStable U → ∀ u ∈ U, B u ∈ U) ∧
      ∀ φ ∈ W, ∀ ψ ∈ W, inner ℂ (cls h (act o φ)) (cls h ψ) = inner ℂ (cls h φ) (cls h (B ψ)))
    {ψ : Sm E N} (hψW : ψ ∈ W) (hψ0 : ψ ≠ 0) :
    ∃ V : Submodule ℂ (Sm E N), IsStable V ∧ V ≤ SupSpansPsiPart W ψ ∧ V ≠ ⊥ ∧
      (∀ U ≤ V, IsStable U → U = ⊥ ∨ U = V) ∧ ∃ v ∈ V, inner ℂ (cls h ψ) (cls h v) ≠ 0 := by
  classical
  obtain ⟨L, hLo, hLc, hψT⟩ := exists_type (hA ψ hψW)
  have : FiniteDimensional ℂ (orbSpan ψ) := (hA ψ hψW).kfin
  have hρ := isContRep_sub (orbSpan ψ) (orbSpan_stable ψ)
  set ρ := sub (cptRep E N) (orbSpan ψ) (orbSpan_stable ψ)
  set T := typePart L ρ
  set A := SupSpansPsiPart W ψ
  have hAst : IsStable A := isStable_admissible_span hW ψ
  have hAW : A ≤ W := admissible_span_le W ψ
  have hfd : ∀ V' ≤ A, FiniteDimensional ℂ (V' ⊓ T : Submodule ℂ (Sm E N)) := fun V' h' =>
    haveI := finiteDimensional_admissible_isotypic hA (hA ψ hψW) hLo ρ hρ
    Submodule.finiteDimensional_of_le (inf_le_inf_right T h')
  let Cand : Submodule ℂ (Sm E N) → Prop := fun V' =>
    IsStable V' ∧ V' ≤ A ∧ ∃ v ∈ V' ⊓ T, inner ℂ (cls h ψ) (cls h v) ≠ 0
  have hψψ : inner ℂ (cls h ψ) (cls h ψ) ≠ 0 := fun e => hψ0 (hinj ψ hψW (inner_self_eq_zero.1 e))
  have hex : ∃ n, ∃ V', Cand V' ∧ Module.finrank ℂ (V' ⊓ T : Submodule ℂ (Sm E N)) = n :=
    ⟨_, A, ⟨hAst, le_rfl, ψ, ⟨mem_admissible_span_self hψW, hψT⟩, hψψ⟩, rfl⟩
  obtain ⟨V1, hV1, hV1n⟩ := Nat.find_spec hex
  have hmin : ∀ V', Cand V' → Nat.find hex ≤ Module.finrank ℂ (V' ⊓ T : Submodule ℂ (Sm E N)) :=
    fun V' hV' => Nat.find_min' hex ⟨V', hV', rfl⟩
  let V0 := sInf {U : Submodule ℂ (Sm E N) | IsStable U ∧ V1 ⊓ T ≤ U}
  have hV0st : IsStable V0 := isStable_sInf _ fun U hU => hU.1
  have hV0le : V0 ≤ V1 := sInf_le ⟨hV1.1, inf_le_left⟩
  have hgen : ∀ U, IsStable U → V1 ⊓ T ≤ U → V0 ≤ U := fun U hU hle => sInf_le ⟨hU, hle⟩
  have hTV0 : V1 ⊓ T ≤ V0 := le_sInf fun U hU => hU.2
  have hV0T : V0 ⊓ T = V1 ⊓ T := le_antisymm (inf_le_inf_right T hV0le) (le_inf hTV0 inf_le_right)
  have hV0A : V0 ≤ A := hV0le.trans hV1.2.1
  obtain ⟨v, hvT, hvψ⟩ := hV1.2.2
  have hvT0 : v ∈ V0 ⊓ T := hV0T ▸ hvT
  have key : ∀ U', Cand U' → U' ≤ V0 → V0 ≤ U' := by
    intro U' hU' hle
    have := hfd V1 hV1.2.1
    have := hfd U' hU'.2.1
    have h1 : U' ⊓ T ≤ V1 ⊓ T := hV0T ▸ inf_le_inf_right T hle
    have h2 : Module.finrank ℂ (V1 ⊓ T : Submodule ℂ (Sm E N)) ≤ Module.finrank ℂ (U' ⊓ T : Submodule ℂ (Sm E N)) :=
      hV1n ▸ hmin U' hU'
    have h3 : U' ⊓ T = V1 ⊓ T := Submodule.eq_of_le_of_finrank_le h1 h2
    exact hgen U' hU'.1 (h3 ▸ inf_le_left)
  refine ⟨V0, hV0st, hV0A, fun e => ?_, fun U hU hUst => ?_, v, hvT0.1, hvψ⟩
  · have hv0 : v = 0 := (Submodule.mem_bot ℂ).1 (e ▸ hvT0.1)
    rw [hv0] at hvψ
    exact hvψ (by rw [show (0 : Sm E N) = (0 : ℂ) • (0 : Sm E N) by simp, cls_smul h 0 W.zero_mem, zero_smul,
      inner_zero_right])
  · let C := orthIn h V0 U (hV0A.trans hAW)
    have hCst : IsStable C := fun o x hx => ⟨hV0st o x hx.1, fun u hu => by
      obtain ⟨B, hB, hadjB⟩ := hadj o
      rw [hadjB x (hAW (hV0A hx.1)) u (hAW (hV0A (hU hu)))]
      exact hx.2 _ (hB U hUst u hu)⟩
    have := hfd U (hU.trans hV0A)
    obtain ⟨v1, ⟨hv1U, hv1T⟩, hv1⟩ := exists_orth h hW hA hinj hUst (hU.trans (hV0A.trans hAW))
      (hAW (hV0A hvT0.1)) hLo hLc ρ hρ hvT0.2
    have hv2C : v - v1 ∈ C := ⟨V0.sub_mem hvT0.1 (hU hv1U), hv1⟩
    have hv2T : v - v1 ∈ T := T.sub_mem hvT0.2 hv1T
    have hsplit : inner ℂ (cls h ψ) (cls h v) =
        inner ℂ (cls h ψ) (cls h v1) + inner ℂ (cls h ψ) (cls h (v - v1)) := by
      rw [cls_sub h (hAW (hV0A hvT0.1)) (hAW (hV0A (hU hv1U))), inner_sub_right]
      ring
    by_cases hc : inner ℂ (cls h ψ) (cls h v1) = 0
    · left
      have hC : Cand C := ⟨hCst, fun x hx => hV0A hx.1, v - v1, ⟨hv2C, hv2T⟩, by
        rw [hsplit, hc, zero_add] at hvψ
        exact hvψ⟩
      have hV0C := key C hC fun x hx => hx.1
      rw [eq_bot_iff]
      intro u hu
      exact (Submodule.mem_bot ℂ).2 (hinj u (hAW (hV0A (hU hu))) (inner_self_eq_zero.1 ((hV0C (hU hu)).2 u hu)))
    · right
      exact le_antisymm hU (key U ⟨hUst, hU.trans hV0A, v1, ⟨hv1U, hv1T⟩, hc⟩ hU)

end PositivityTheory.Rg.Rs.PrIrr

end
