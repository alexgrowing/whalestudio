import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHeckeOpFullIffIndependentOfBlockLevelStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Hk3 (Core IsSF SchurAll EEc Wcc)

namespace GlobalTheory.TrLevMult

theorem level_eq_trivial {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (L : LevelP Pg r LL) (h : L.H = ⊥) : L = LevelP.triv Pg r LL := by
  obtain ⟨H, chi⟩ := L
  simp only at h
  subst h
  unfold LevelP.triv
  congr 1
  ext x
  have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.2)
  subst hx
  simp

theorem levPOf_bot_eq {D : D7} {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ} (eG : G ≃* G0 Pg r)
    (σ : K →+* ℂ) (ψ : (⊥ : Subgroup G) →* Kˣ) : levPOf eG σ ⊥ ψ = LevelP.triv Pg r ℂ := by
  apply level_eq_trivial
  show Subgroup.comap eG.symm.toMonoidHom ⊥ = ⊥
  ext x
  simp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem pg_over {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSF : IsSF R SF) : ∀ PP ∈ R.Pg, ∃ v ∈ SF,
    PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal :=
  fun PP hPP => ⟨Formalism.IndefR.Fin.belowPl PP, (hSF _).2 ⟨PP, hPP, rfl⟩, rfl⟩

theorem trAt_of_dim (hC : Core R F) {SF} (hSF : IsSF R SF) (i : Fin D.R.m) (Pe Pw : LevelP R.Pg D.R.r ℂ)
    (hdim : ∀ c, Module.finrank ℂ (Wcc R SF i c ⊓ (R.Wat i (sg0 D A) Pw).comap (R.HW i _).e : Submodule ℂ _) =
      Module.finrank ℂ (EEc R SF c ⊓ (R.EEat Pe).comap R.HE.e : Submodule ℂ _)) :
    GlobalTheory.TrCopy.TRAt R SF i Pe Pw := by
  intro c
  have hE : R.EEat Pe ≤ R.EEat R.triv := GlobalTheory.PartDims.goodPart_le_flag (L := R.dat0 R.triv) R.θ _ rfl rfl _ _
  have hW : R.Wat i (sg0 D A) Pw ≤ R.Wat i (sg0 D A) R.triv :=
    GlobalTheory.PartDims.goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _
  have kE : ∀ Q d B, Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) SF Q d B ↔
      Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF Q d B :=
    GlobalTheory.T.isHeckeOpFull_iff_independent_of_blockLevel D (Yc D 0) (R.βY 0) (R.dat0 R.triv) Pe R.triv SF (pg_over hSF)
  have kW : ∀ Q d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw)) SF Q d B ↔
      Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF Q d B :=
    GlobalTheory.T.isHeckeOpFull_iff_independent_of_blockLevel D (Wc D i) (R.βW i) (R.datWp i R.triv) Pw R.triv SF (pg_over hSF)
  have eqE : GlobalTheory.TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) R.e0 SF c =
      R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF
        (fun Q d => c Q (dualLab d)) := by
    ext x
    show (x ∈ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) SF
        (fun Q d => c Q (dualLab d)) ∧ x ∈ R.EEat Pe) ↔ (x ∈ R.EEat Pe ∧ x ∈ partFull R.θ (R.MY 0)
        (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d)))
    simp only [partFull, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, (hE h2).1, fun Q d B hB => h1 Q d B ((kE Q d B).2 hB)⟩
    · rintro ⟨h2, -, h1⟩
      exact ⟨⟨h2.1, fun Q d B hB => h1 Q d B ((kE Q d B).1 hB)⟩, h2⟩
  have eqW : GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw))
        (R.eWf i (sg0 D A)) SF c =
      R.Wat i (sg0 D A) Pw ⊓ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
        (levChi _ (R.βW i) (R.datWp i R.triv)) SF c := by
    ext x
    show (x ∈ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw)) SF c ∧
        x ∈ R.Wat i (sg0 D A) Pw) ↔ (x ∈ R.Wat i (sg0 D A) Pw ∧ x ∈ partFull R.θ (R.MW i (sg0 D A))
        (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c)
    simp only [partFull, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, (hW h2).1, fun Q d B hB => h1 Q d B ((kW Q d B).2 hB)⟩
    · rintro ⟨h2, -, h1⟩
      exact ⟨⟨h2.1, fun Q d B hB => h1 Q d B ((kW Q d B).1 hB)⟩, h2⟩
  have fE := GlobalTheory.PartDims.finrank_comap hC.models.HE (U := R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d))) (inf_le_left.trans hE)
  have fW := GlobalTheory.PartDims.finrank_comap (hC.models.HW i (sg0 D A)) (U := R.Wat i (sg0 D A) Pw ⊓
    partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c)
    (inf_le_left.trans (hW.trans inf_le_left))
  have cE : (R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d))).comap R.HE.e =
      EEc R SF c ⊓ (R.EEat Pe).comap R.HE.e := by
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  have cW : (R.Wat i (sg0 D A) Pw ⊓ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) SF c).comap (R.HW i _).e =
      Wcc R SF i c ⊓ (R.Wat i (sg0 D A) Pw).comap (R.HW i _).e := by
    ext x
    exact ⟨fun hx => ⟨⟨hW hx.1, hx.2⟩, hx.1⟩, fun hx => ⟨hx.2, hx.1.2⟩⟩
  haveI := fE.2
  haveI := fW.2
  show Module.rank ℂ (GlobalTheory.TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) R.e0 SF c) =
    Module.rank ℂ (GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw))
        (R.eWf i (sg0 D A)) SF c)
  rw [eqE, eqW, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← fE.1, ← fW.1, cE, cW, hdim c]

end GlobalTheory.TrLevMult

open GlobalTheory.TrLevMult in

theorem GlobalTheory.TrLevMult.trLev_of_multEq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F s hs hC hS hX hD hM SF hSF
  have key : ∀ i (P : Subgroup G) (ψ : P →* D.what₂.LLˣ),
      GlobalTheory.TrCopy.TRAt R SF i (levPOf R.eG D.what₂.embLL P ψ) (levPOf R.eG (sg0 D A) P ψ⁻¹) :=
    fun i P ψ => trAt_of_dim hC hSF i _ _ (fun c => GlobalTheory.DimFull.dim_parts_full R F hs hC hS hX hD hM SF hSF P ψ i c)
  intro i
  refine ⟨?_, fun b => key i _ _⟩
  have h := key i ⊥ 1
  rwa [inv_one, levPOf_bot_eq, levPOf_bot_eq] at h

end
