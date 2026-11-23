import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOSmulHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDualStep

variable {D : D7}

theorem actO_one_left (S T : HSp D) (h : GA D T) (Z : WO S T) :
    actO S T 1 h Z = HMul.hMul (Formalism.L2.Theta.mt T h) (Z : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
  unfold actO
  simp [Formalism.L2.Theta.mt]

theorem infPart_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : infPart D e = 0 := by
  classical
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  subst hsum
  induction P using Finset.induction_on with
  | empty => rw [Finset.sum_empty, RingHom.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, RingHom.map_add, GlobalTheory.SplitScalar.infPart_splitIdem (hes a (Finset.mem_insert_self a s)).1,
      ih fun PP hPP => hes PP (Finset.mem_insert_of_mem hPP), add_zero]

def finLift {m n : ℕ} (c : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  Matrix.of fun a b => pairA D.host.F 0 1 ⊗ₜ[D.host.F] c a b

theorem smul_map_incA {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {m n : ℕ}
    (c : Matrix (Fin m) (Fin n) D.host.E) :
    e • c.map (incA D) = e • finLift c := by
  ext a b
  simp only [finLift, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [map_mul, map_mul, infPart_idemSum he, zero_mul, zero_mul]
  · rw [map_mul, map_mul, GlobalTheory.LatVac.finPart_pair, GlobalTheory.LatVac.finPart_incA]

theorem homLat_mul {a b c : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin c → D.host.E)}
    {x : Matrix (Fin c) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin a) D.host.E}
    (hx : x ∈ homLat Λ' Λ'') (hy : y ∈ homLat Λ Λ') : x * y ∈ homLat Λ Λ'' := by
  show ∀ v ∈ Λ, (x * y) *ᵥ v ∈ Λ''
  intro v hv
  rw [← Matrix.mulVec_mulVec]
  exact hx _ (hy v hv)

theorem smul_homLat_mul {a b c : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin c → D.host.E)}
    {x : Matrix (Fin c) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin a) D.host.E}
    (hx : x ∈ 𝔪 • homLat Λ' Λ'') (hy : y ∈ homLat Λ Λ') : x * y ∈ 𝔪 • homLat Λ Λ'' := by
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun p q hp hq => ?_)
  · rw [Matrix.smul_mul]
    exact Submodule.smul_mem_smul hr (homLat_mul hn hy)
  · rw [Matrix.add_mul]
    exact Submodule.add_mem _ hp hq

theorem hatMx_mul {a b c : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin c) (Fin b) D.host.E)}
    {N : Submodule (𝓞 D.host.E) (Matrix (Fin c) (Fin a) D.host.E)} (y : Matrix (Fin b) (Fin a) D.host.E)
    (hMN : ∀ x ∈ M, x * y ∈ N) {u : Mx D c b} (hu : u ∈ hatMx M) : u * y.map (incA D) ∈ hatMx N := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, x * y, hMN x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show _ * (Algebra.TensorProduct.includeRight (y k j)) = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add p q _ _ hp hq => rw [Matrix.add_mul]; exact add_mem hp hq
  | neg p _ hp => rw [Matrix.neg_mul]; exact neg_mem hp

theorem smul_one_sub {n : ℕ} (e : AE D) (A A' C : Matrix (Fin n) (Fin n) (AE D)) (h : e • A = e • C) :
    e • (1 - (A' - C)) = e • (1 + A - A') := by
  rw [smul_sub, smul_sub, smul_sub, smul_add, h]
  abel

theorem core_step {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n n' : ℕ}
    (x₀ : Matrix (Fin n) (Fin n') D.host.E) (y₀ : Matrix (Fin n') (Fin n) D.host.E)
    (mg : Matrix (Fin n) (Fin n) (AE D)) (u u' : Matrix (Fin n) (Fin n') (AE D))
    (heq : e • (x₀.map (incA D) - u) = HMul.hMul mg (e • (x₀.map (incA D) - u'))) :
    e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul u (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1))) =
      HMul.hMul mg (e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul u' (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1)))) := by
  have hxy : x₀ * y₀ = 1 + (x₀ * y₀ - 1) := by abel
  have hXY : HMul.hMul (x₀.map (incA D)) (y₀.map (incA D)) = (1 : Matrix (Fin n) (Fin n) (AE D)) + (x₀ * y₀ - 1).map (incA D) := by
    rw [← Matrix.map_mul]
    conv_lhs => rw [hxy]
    rw [Matrix.map_add (incA D) (fun a b => RingHom.map_add _ a b),
      Matrix.map_one (incA D) (RingHom.map_zero _) (RingHom.map_one _)]
  have hce := smul_map_incA he (x₀ * y₀ - 1)
  have key : ∀ v : Matrix (Fin n) (Fin n') (AE D),
      e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul v (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1))) =
        HMul.hMul (e • (x₀.map (incA D) - v)) (y₀.map (incA D)) := by
    intro v
    rw [Matrix.smul_mul, Matrix.sub_mul, hXY]
    exact smul_one_sub e _ _ _ hce
  rw [key u, key u', heq, Matrix.mul_assoc]

theorem coset_equation_mul_right_congruent_one_mod_depthIdeal : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ u ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∀ u' ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))),
    e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u')) →
    ∃ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∃ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
      e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) := by
  intro D _ T L μ0 _ sc G W M _ i _ x₀ hx₀ e he g u hu u' hu' heq
  obtain ⟨-, y₀, hy₀, hc⟩ := hx₀
  have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by simp
  have hcf : finLift (x₀ * y₀ - 1) ∈
      hatMx (G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i))) :=
    AddSubgroup.subset_closure ⟨1, h1, x₀ * y₀ - 1, hc, rfl⟩
  have hmul : ∀ x ∈ G.modul • homLat (G.latS (.core i)) (G.latT (.core i)),
      x * y₀ ∈ G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i)) := fun x hx => smul_homLat_mul hx hy₀
  refine ⟨_, sub_mem (hatMx_mul y₀ hmul hu) hcf, _, sub_mem (hatMx_mul y₀ hmul hu') hcf, ?_⟩
  rw [actO_one_left] at heq ⊢
  exact core_step he x₀ y₀ _ u u' heq

end GlobalTheory.CosDualStep
