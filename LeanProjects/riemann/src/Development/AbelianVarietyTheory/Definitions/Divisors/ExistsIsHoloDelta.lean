import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HoloOcc
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolCap
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExistsIdele
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DirChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.OrthCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCT
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftExp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.HkCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.InfGLScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatHol
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformModel

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
open scoped Matrix Manifold UpperHalfPlane

namespace GlobalTheory.TfJl

def lamDelta : InfinitePlace ℚ → DomWeight 2 := fun _ =>
  ⟨![5, -5], fun i j h => by fin_cases i <;> fin_cases j <;> simp_all⟩

theorem exists_isHolo_delta : ∃ φ : TR.Sm ℚ 2, φ ≠ 0 ∧ IsHolo lamDelta φ ∧ ∀ u ∈ K1G 1, TR.finRep ℚ 2 u φ = φ := by
  let g := deltaNewform
  let f := g.f
  have hM : 1 ≤ g.M := g.pos
  obtain ⟨ω, hω⟩ := dirChar g.M hM g.χ
  obtain ⟨φ₀, hφ⟩ := liftEx 12 g.M hM f fun δ hδ => SlashInvariantForm.slash_action_eqn f δ ⟨δ, hδ, rfl⟩
  obtain ⟨hl, hr, hs⟩ := liftSm 12 g.M hM f φ₀ hφ
  let φ : TR.Sm ℚ 2 := ⟨φ₀, hs f.holo'⟩
  have hfix : ∀ u ∈ K1G g.M, TR.finRep ℚ 2 u φ = φ := fun u hu => Subtype.ext (funext (hr u hu))
  have hlev : IsOpen {u | TR.finRep ℚ 2 u φ = φ} :=
    isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset ((kOpen g.M hM).1.mem_nhds (one_mem _)) hfix)
  have hc := liftCent 12 g.M hM g.χ ω hω f g.char φ₀ hφ
  have hlie := liftLie 12 g.M hM f f.holo' φ hφ
  obtain ⟨C, hC⟩ := archBd 12 g.M hM f
  have hfin := (charVal g.M hM g.χ ω hω).1
  have haut : TR.IsAutForm φ := ⟨hl, hlev, liftK 12 g.M hM f φ hφ,
    zFin ℚ 12 ω hfin φ hc (fun v => (hlie v).1) (fun v => (hlie v).2), fun x => ⟨C, 0, fun y => by
      obtain ⟨γ, h, u, hu, e⟩ := decomp g.M hM (x * TR.infGL ℚ 2 y)
      rw [pow_zero, mul_one, e]
      change ‖φ₀ _‖ ≤ C
      rw [hφ γ h u hu]
      exact hC _ h.det_ne_zero⟩⟩
  have hH : IsHol 12 (lev g.M) ω φ :=
    ⟨haut, fun w u hu => hfix _ (kLocal g.M hM w u hu), hc, fun v => (hlie v).1, fun v => (hlie v).2⟩
  have hE := liftExp 12 g.M hM f φ.1 hφ
  obtain ⟨-, hz, -⟩ := Sd.holLin ℚ 12 (lev g.M) ω
  refine ⟨φ, fun e => ?_, ⟨⟨haut, cuspCrit φ hl hlev (liftCT 12 g.M hM f φ₀ hφ)⟩, fun v => ⟨?_, (hlie v).2, fun u => ?_⟩⟩, hfix⟩
  · rw [e] at hE
    have := (Sd.expUnique ℚ _ 12 _ _ _ _ hE hz).2 ⊤ top_ne_bot
    rw [icoef, Ideal.absNorm_top, g.one] at this
    exact one_ne_zero this
  · rw [(hlie v).1]
    simp [kw, lamDelta]
  · rw [(Sd.holCap ℚ 12 _ ω hfin φ hH).2 v u, GlobalTheory.UnitaryBC.infOfWeight, Multiset.map_map, Multiset.map_map,
      ← Finset.prod_eq_multiset_prod, Fin.prod_univ_two]
    congr 1
    simp [lamDelta]
    ring

end GlobalTheory.TfJl
