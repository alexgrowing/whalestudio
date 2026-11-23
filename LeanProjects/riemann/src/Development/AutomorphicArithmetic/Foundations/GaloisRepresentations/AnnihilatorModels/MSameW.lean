import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isMonHom_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

private theorem pow_hom_comm {S : Scheme.{0}} {A : Over S} [GrpObj A] (h : A ⟶ A) [IsMonHom h] (n : ℕ) :
    h ≫ ((𝟙 A) ^ n) = ((𝟙 A) ^ n) ≫ h := by
  induction n with
  | zero => simp [Hom.one_def]
  | succ n ih =>
    simp only [pow_succ, Hom.mul_def, comp_lift_assoc, Category.assoc, IsMonHom.mul_hom, lift_map_assoc, Category.comp_id, Category.id_comp, ih]

theorem UpperTheory.Gal.crystallineComparison.Mod.sameW_of :
    KillLocal → InfW → FrobPass → KerU → RepOfFF → TanOne → SameW := by
  intro hKL hInf hFP hKU hRep hTan
  intro p _ D R _ b N hm ha r w hw hu f κ _ _ _ β hβ o o₁ o₂ o₃ ψ₁ ψ₂ F e h1 hψ₂ h3 hF d hd hR1 hc1 hR2 hc2 hcl T g
  have hp : Nat.Prime p := Fact.out
  obtain ⟨-, hm1, hact1, -, -, ψ₁', hψ₁', h11, h12⟩ := h1
  obtain ⟨-, hm3, hact3, -, -, χ', hχ', h31, h32⟩ := h3
  haveI := hm1
  haveI := hm3
  haveI := hψ₁'
  haveI := hχ'
  haveI := hψ₂
  haveI hpow : IsMonHom ((𝟙 o.A) ^ p ^ (e + 1)) := isMonHom_pow o.A _
  have hactP : ∀ a : D.O, o.act.act a ≫ ((𝟙 o.A) ^ p ^ (e + 1)) = ((𝟙 o.A) ^ p ^ (e + 1)) ≫ o.act.act a := by
    intro a
    haveI := o.act.hom a
    exact pow_hom_comm (o.act.act a) _
  have kP := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o ((𝟙 o.A) ^ p ^ (e + 1)) (𝟙 o.A) (e + 1)
    hpow inferInstance hactP (by simp) (by simp)
  obtain ⟨d', hRP⟩ := hRep κ o.A _ kP.1
  have k1 := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o₁ ψ₁ ψ₁' (e + 1) hm1 hψ₁' hact1 h11 h12
  have k3 := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o₃ (ψ₂ ≫ F) χ' (e + 1) hm3 hχ' hact3 h31 h32
  obtain ⟨d₃, hR3⟩ := hRep κ o.A _ k3.1
  have sub1 : ∀ (T : Over (Sp κ)) (g : T ⟶ o.A), UKer r o ψ₁ T g → UKer r o ((𝟙 o.A) ^ p ^ (e + 1)) T g := by
    intro T g hg
    refine ⟨?_, hg.2⟩
    rw [← h11, ← Category.assoc, hg.1]
    simp [Hom.one_def]
  have sub3 : ∀ (T : Over (Sp κ)) (g : T ⟶ o.A), UKer r o (ψ₂ ≫ F) T g → UKer r o ((𝟙 o.A) ^ p ^ (e + 1)) T g := by
    intro T g hg
    refine ⟨?_, hg.2⟩
    rw [← h31, ← Category.assoc, hg.1]
    simp [Hom.one_def]
  have hI := hInf p f hp κ o.A (UKer r o ψ₁) (UKer r o ((𝟙 o.A) ^ p ^ (e + 1))) d d' hR1 k1.2.1 hc1 hd hRP sub1
    (hTan p D R b N hm ha r w hu κ β hβ o e)
  have fp := hFP p D R b N r f κ (spMap β) o o₂ ψ₂ hψ₂ d hR2 hc2
  have hF1 : (1 : 𝟙_ (Over (Sp κ)) ⟶ o₂.A) ≫ F = 1 := (hF _ 1).2 (fun _ => rfl)
  constructor
  · intro hg
    refine ⟨?_, hg.2⟩
    refine hKL κ o.A o₃.A (ψ₂ ≫ F) hm3 (UKer r o ψ₁) (p ^ f * d) hR1 k1.2.1 ?_ ?_ T g hg
    · intro g' hg'
      rw [← Category.assoc, ((hcl g').1 hg').1, hF1]
    · intro Λ _ _ _ ε g' hg' hi
      rw [← Category.assoc]
      exact (hF _ _).2 ((fp.2 Λ ε g' hg'.2 hi).2 ((hI Λ ε g' (sub1 _ _ hg') hi).1 hg'))
  · intro hg
    refine ⟨?_, hg.2⟩
    refine hKL κ o.A o₁.A ψ₁ hm1 (UKer r o (ψ₂ ≫ F)) d₃ hR3 k3.2.1 ?_ ?_ T g hg
    · intro g' hg'
      have h2 : g' ≫ ψ₂ = 1 := fp.1 (g' ≫ ψ₂) ((hF _ _).1 (by rw [Category.assoc]; exact hg'.1))
      exact ((hcl g').2 ⟨h2, hg'.2⟩).1
    · intro Λ _ _ _ ε g' hg' hi
      have hk : FrobKill p f hp (g' ≫ ψ₂) := (hF _ _).1 (by rw [Category.assoc]; exact hg'.1)
      exact ((hI Λ ε g' (sub3 _ _ hg') hi).2 ((fp.2 Λ ε g' hg'.2 hi).1 hk)).1
