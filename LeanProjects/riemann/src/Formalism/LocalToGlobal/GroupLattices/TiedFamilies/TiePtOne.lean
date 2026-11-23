import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {p : ℕ} {G : GAtP p} {A : LocAt F E n G}

def LocInt (A : LocAt F E n G) : Prop :=
  ∀ v (x : G.P.Qq v), x ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔ A.eQ v x ∈ (A.pl v).1.adicCompletionIntegers F

def LocHyp (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) : Prop :=
  ∀ v (x : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)), x ∈ UPts σ J ((A.pl v).1.adicCompletion F) →
    (∀ a b, (((bc (A.phE v) A.B)⁻¹ * bc (A.ph v) x * bc (A.phE v) A.B : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F) →
    (∀ a b, ((((bc (A.phE v) A.B)⁻¹ * bc (A.ph v) x * bc (A.phE v) A.B)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F) → x ∈ S.Uloc (A.pl v).1

theorem int_of_stab (hW : LocInt A) (v : Fin G.P.nV) (h : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hh : ∀ a b, (h : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) a b ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range)
    (a b : Fin n) :
    (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) h) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F := by
  have h1 : (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) h) : Matrix (Fin n) (Fin n) _) a b =
      A.eQ v ((castGL A.rk (G.P.Qq v) h : Matrix (Fin n) (Fin n) _) a b) := rfl
  rw [h1, castGL_apply]
  exact (hW v _).1 (hh _ _)

theorem locHyp_of {k : ℕ} (hk : k = n) (A : LocAt F E n G) (S : StepLevel F E σ J T f bad) (J0 : Matrix (Fin k) (Fin k) E)
    (hJ : ∀ x y, J x y = J0 (Fin.cast hk.symm x) (Fin.cast hk.symm y)) (B0 : GL (Fin k) E) (hB : A.B = reGL hk E B0)
    (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin k) (E ⊗[F] v.adicCompletion F)))
    (hU : ∀ v, S.Uloc v = (Uloc0 v).map (reGL hk _).toMonoidHom)
    (h0 : ∀ v (x : GL (Fin k) (E ⊗[F] (A.pl v).1.adicCompletion F)), x ∈ UPts σ J0 ((A.pl v).1.adicCompletion F) →
      (∀ a b, (((bc (A.phE v) B0)⁻¹ * bc (A.ph v) x * bc (A.phE v) B0 : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) a b ∈
        (A.pl v).1.adicCompletionIntegers F) →
      (∀ a b, ((((bc (A.phE v) B0)⁻¹ * bc (A.ph v) x * bc (A.phE v) B0)⁻¹ : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) a b ∈
        (A.pl v).1.adicCompletionIntegers F) → x ∈ Uloc0 (A.pl v).1) : LocHyp S A := by
  subst hk
  obtain rfl : J = J0 := by ext x y; exact hJ x y
  have hre : ∀ (R : Type) [CommRing R] (g : GL (Fin k) R), reGL (rfl : k = k) R g = g := by
    intro R _ g; apply Units.ext; ext x y; rfl
  rw [hre] at hB
  intro v x hx h1 h2
  rw [hB] at h1 h2
  rw [hU]
  exact Subgroup.mem_map.2 ⟨x, h0 v x hx h1 h2, hre _ x⟩

theorem ptOne_of (S : StepLevel F E σ J T f bad) (hW : LocInt A) (hH : LocHyp S A)
    (hbad : ∀ w ∈ bad, ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) : PtOne S G A := by
  intro i L g g' x x' hL hL' hx hx'
  have hoff : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) (x.1⁻¹ * x'.1) = 1 := by
    intro w hw
    rw [map_mul, map_inv, hx.1 w hw, hx'.1 w hw, inv_mul_cancel]
  have hmem : x.1⁻¹ * x'.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) x'.2
  have hU : x.1⁻¹ * x'.1 ∈ S.U := by
    rw [S.U_eq]
    refine ⟨hmem, fun w => ?_⟩
    by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
    · obtain ⟨v, rfl⟩ := LocGood.exists_pl A w hw
      have hst : (g v)⁻¹ * g' v ∈ stabStd (k := G.P.m + 1) (Qq := G.P.Qq v) (G.P.W v) := by
        rw [← gMap_std_eq_iff, ← colSpan_eq, ← colSpan_eq, ← hL v, ← hL' v]
      have e : (bc (A.phE v) A.B)⁻¹ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (x.1⁻¹ * x'.1)) * bc (A.phE v) A.B =
          bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) ((g v)⁻¹ * g' v)) := by
        rw [map_mul, map_mul, map_inv, map_inv, hx.2 v, hx'.2 v, map_mul, map_mul, map_inv, map_inv]
        group
      obtain ⟨h1, h2⟩ := (stabStd_iff _ _).1 hst
      refine hH v _ (Formalism.UG.P.afsplit_bc_mem σ J (A.pl v).1 _ hmem) ?_ ?_
      · rw [e]
        exact int_of_stab hW v _ h1
      · rw [e, ← map_inv, ← map_inv]
        exact int_of_stab hW v _ h2
    · rw [hoff w hw]
      exact Subgroup.one_mem _
  refine ⟨⟨_, hU⟩, by group, ?_⟩
  rw [S.chi_triv ⟨_, hU⟩ fun w hw => hoff w (hbad w hw)]
  rfl

end Formalism.L2.G
