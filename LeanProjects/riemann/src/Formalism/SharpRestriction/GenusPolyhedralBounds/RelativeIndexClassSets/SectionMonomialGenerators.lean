import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FirstLengthLePrimeBound
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocalFormOfWeakForm
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevelsQDesc

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Base

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (ka : WeightFamilies.Wt D j)

theorem bcV_mem_Vw {x : X.Vl la} (hx : x ∈ T0.WL X ka la) : bcV X la N x ∈ Vw X la N ka := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, ⟨F', _, rfl⟩, rfl⟩ := hx
    exact emb_mem_Vw X la N ka F'
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul, ← algebraMap_smul (Kp X la N) a]
    exact Submodule.smul_mem _ _ hx

def jW : ↥(T0.WL X ka la) →ₗ[X.Kl la] ↥(Vw X la N ka) :=
  ((bcV X la N).toLinearMap.domRestrict (T0.WL X ka la)).codRestrict ((Vw X la N ka).restrictScalars (X.Kl la))
    fun x => bcV_mem_Vw X la N ka x.2

theorem coe_jW (x : ↥(T0.WL X ka la)) : (jW X la N ka x : Rp X la N) = bcV X la N (x : X.Vl la) := rfl

def M1 : Submodule (Op X la N) ↥(Vw X la N ka) :=
  Submodule.span (Op X la N) (jW X la N ka '' (T0.MW X ka la : Set ↥(T0.WL X ka la)))

def Th1 (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T : ℕ) : Submodule (Op X la N) ↥(Vw X la N ka) :=
  Submodule.span (Op X la N) (jW X la N ka '' (T0.ThW X S ka wL wF T la : Set ↥(T0.WL X ka la)))

def MggO (B : WeightFamilies.Prov D) (CRm T c : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j) : Submodule (𝓞 B.KO) (B.Cusp j ka) :=
  B.Mlat j ka ⊓ (WeightFamilies.MggK B CRm T c j ka).restrictScalars (𝓞 B.KO)

def MggW (CRm T c : ℝ) : Submodule (X.Ol la) ↥(T0.WL X ka la) :=
  T0.inW X ka la (X.loc la (X.emb ka (MggO B CRm T c j ka)))

def toW (F : B.Mlat j ka) : ↥(T0.WL X ka la) :=
  ⟨X.bc la (X.inc ka F), Submodule.subset_span ⟨X.inc ka F, ⟨F, F.2, rfl⟩, rfl⟩⟩

end Base

section Chain

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO))

def sectionMonomialGenerators : Set ↥(Vw X la G.N (addL wF wL T)) :=
  {f | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
      (f : Rp X la G.N) = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))}

def N1 : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Op X la G.N) (sectionMonomialGenerators G la)

def Zg : Set ↥(Vw X la G.N (addL wF wL T)) := {f | ∃ k : Fin G.rz, (f : Rp X la G.N) = zK G la k}

def Zl : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Op X la G.N) (Zg G la)

def ZK : Submodule (Kp X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Kp X la G.N) (Zg G la)

def NovK : Submodule (Kp X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  Submodule.span (Kp X la G.N) ((N1 G la ⊔ Zl G la : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T))) :
    Set ↥(Vw X la G.N (addL wF wL T)))

def Zm : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  M1 X la G.N (addL wF wL T) ⊓ (ZK G la).restrictScalars (Op X la G.N)

def Np (e : ℕ) : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  ((M1 X la G.N (addL wF wL T)).map ((unifO X la G.N ^ e) •
      (LinearMap.id : ↥(Vw X la G.N (addL wF wL T)) →ₗ[Op X la G.N] ↥(Vw X la G.N (addL wF wL T)))) ⊓
    (NovK G la).restrictScalars (Op X la G.N)) ⊔ N1 G la ⊔ Zm G la

def rhoO : ↥(Vw X la G.N (addL wF wL T)) →ₗ[Op X la G.N] WK X la G.w wF (a0 D j T) :=
  (rhoK X la G.w wF (a0 D j T) T).restrictScalars (Op X la G.N)

def rhoN (e : ℕ) : ↥(Np G la e) →ₗ[Op X la G.N] WK X la G.w wF (a0 D j T) :=
  rhoO G la ∘ₗ (Np G la e).subtype

theorem reducedGenerators_eq_map : firstLength_le_prime_bound G la T = (N1 G la).map (rhoO G la) := by
  unfold firstLength_le_prime_bound N1
  rw [Submodule.map_span]
  rfl

end Chain

end Formalism.MainNotions.Gaps.EtaleWeightGaps
