import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AbsInvOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.EtaleMapFirstChern

open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.ePin :
    ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (G : Model l K → Prop) (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (e : E.EtFam l K), e.Good → ∃ e' : EMap G (dat Amp), ∀ (M : Model l K) (a : (dat Amp).Ch M) (j : ℕ) (v : M.T j) (n : ℕ), (show (M.MS j).lim from e'.e a j v).1 n = e M n j (v.lev n) := by
  intro l _ K G Amp e he
  refine ⟨{
    e := fun {M} _ j => GlueE.eMap e he.red M j
    lin := fun {M} _ _ j z v => GlueE.eMap_lin e he.red M j (per l K).z z v
    act := fun {M} _ _ j _ v => GlueE.eMap_act e he.red he.equi M j _ v
    phi := fun {M} _ _ j v => GlueE.eMap_phi e he.red he.phi M j v
    nat := fun {_ _ u hu _ _} _ _ _ j v => GlueE.eMap_nat e he.red he.nat u hu j v
    cup := fun {M} _ _ _ _ x y z h => GlueE.eMap_cup e he.red he.cup M x y z h
    one := fun {M} _ _ => GlueE.eMap_one e he.red he.one M
    c1 := fun {M} a _ => GlueE.etale_map_first_chern e he.red he.c1 M a.1 (per l K).t rfl }, ?_⟩
  intro M a j v n
  rfl
