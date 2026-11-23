import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogSt
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfQdetMem

noncomputable section

open NumberField Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

section Quot

variable {M : Type} [AddCommGroup M] [Module ℂ M] (V I : Submodule ℂ M)

def Pa : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {T | (∀ v ∈ V, T v ∈ V) ∧ ∀ v ∈ I, T v ∈ I}
  mul_mem' := fun {_ _} hS hT => ⟨fun v hv => hS.1 _ (hT.1 v hv), fun v hv => hS.2 _ (hT.2 v hv)⟩
  add_mem' := fun {_ _} hS hT => ⟨fun v hv => V.add_mem (hS.1 v hv) (hT.1 v hv), fun v hv => I.add_mem (hS.2 v hv) (hT.2 v hv)⟩
  algebraMap_mem' := fun c => ⟨fun _ hv => V.smul_mem c hv, fun _ hv => I.smul_mem c hv⟩

def piQ : Pa V I →ₐ[ℂ] Module.End ℂ (V ⧸ I.comap V.subtype) where
  toFun T := (I.comap V.subtype).mapQ (I.comap V.subtype) (T.1.restrict T.2.1) (fun v hv => T.2.2 _ hv)
  map_one' := by
    ext v
    rfl
  map_mul' S T := by
    ext v
    rfl
  map_zero' := by
    ext v
    rfl
  map_add' S T := by
    ext v
    rfl
  commutes' c := by
    ext v
    rfl

theorem piQ_eq_zero {T : Pa V I} (h : piQ V I T = 0) : ∀ v ∈ V, T.1 v ∈ I := by
  intro v hv
  have e := LinearMap.congr_fun h (Submodule.Quotient.mk ⟨v, hv⟩)
  rw [LinearMap.zero_apply] at e
  change Submodule.Quotient.mk (T.1.restrict T.2.1 ⟨v, hv⟩) = 0 at e
  rw [Submodule.Quotient.mk_eq_zero] at e
  exact e

theorem piQ_eq_algebraMap {T : Pa V I} (c : ℂ) (h : ∀ v ∈ V, T.1 v - c • v ∈ I) : piQ V I T = algebraMap ℂ _ c := by
  ext v
  change Submodule.Quotient.mk (T.1.restrict T.2.1 v) = Submodule.Quotient.mk (c • v)
  rw [Submodule.Quotient.eq]
  exact h v.1 v.2

end Quot

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def Sl (N : ℕ) : Subalgebra ℂ (Module.End ℂ (Sm E N)) := Algebra.adjoin ℂ (Set.range (lie E N))

theorem lie_mem_Sl {N : ℕ} (X : Lie E N) : lie E N X ∈ Sl (E := E) N := Algebra.subset_adjoin ⟨X, rfl⟩

theorem Eop_mem_Sl {N : ℕ} (τ : E →+* ℂ) (i j : Fin N) : Eop τ i j ∈ Sl (E := E) N := by
  have h1 : lieS E N i j (atEmb τ 1) ∈ Sl (E := E) N := by rw [lieS_apply]; exact lie_mem_Sl _
  have h2 : lieS E N i j (atEmb τ Complex.I) ∈ Sl (E := E) N := by rw [lieS_apply]; exact lie_mem_Sl _
  have e : Eop τ i j = (1 / 2 : ℂ) • (lieS E N i j (atEmb τ 1) - Complex.I • lieS E N i j (atEmb τ Complex.I)) := rfl
  rw [e]
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ h1 (Subalgebra.smul_mem _ h2 _)) _

theorem qdet_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) {n : ℕ} (X : Fin n → Fin n → A)
    (hX : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hX _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem Sl_comm_cap {N : ℕ} (τ : E →+* ℂ) (u : ℂ) {T : Module.End ℂ (Sm E N)} (hT : T ∈ Sl N) :
    Commute (cap τ u) T := by
  have hle : Sl (E := E) N ≤ Subalgebra.centralizer ℂ {cap (a := N) τ u} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨X, rfl⟩
    refine (Subalgebra.mem_centralizer_iff ℂ).2 ?_
    rintro y rfl
    exact (GlobalTheory.SpehInfChar.cap_commute_act τ u (.lie X)).eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl

theorem Sl_comm_ltr {N : ℕ} (h : GA E N) {T : Module.End ℂ (Sm E N)} (hT : T ∈ Sl N) :
    Commute (JFinTr.ltr h) T := by
  have hle : Sl (E := E) N ≤ Subalgebra.centralizer ℂ {JFinTr.ltr h} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨X, rfl⟩
    refine (Subalgebra.mem_centralizer_iff ℂ).2 ?_
    rintro y rfl
    exact (JFinTr.ltr_lie h X).eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

end
