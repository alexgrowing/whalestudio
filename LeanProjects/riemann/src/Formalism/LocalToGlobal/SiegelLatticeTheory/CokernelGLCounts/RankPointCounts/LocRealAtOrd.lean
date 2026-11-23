import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MulConjApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Assembly

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def LocRealAt (p : PlF D) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)), IsLCls M δ (D.mem u).A.T (D.mem u').A.T p w O →
    ∃ (Lp Up : MatP D p) (c : 𝓞 D.host.F), c ≠ 0 ∧ IsLo Lp ∧ IsUp Up ∧
      ∀ L U : PairVal.MatR D, IsLo L → IsUp U →
        (∀ a b, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (L a b) - Lp a b =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) →
        (∀ a b, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (U a b) - Up a b =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) →
        tupZ M δ u u' (L * ptMat w * U * Sg D.host.E D.R.rS) p = O

variable {M δ}

theorem locRealAt_ord (hA : ∀ p, Agree δ M p) (p : PlF D) (hM : (M p).split = none) : LocRealAt M δ u u' p :=
  fun w O hO => locReal_ord hA u u' w p hM O hO

theorem adj_mem {R : Type*} [CommRing R] (S : Subring R) {n : ℕ} {l : Matrix (Fin n) (Fin n) R}
    (hl : ∀ a b, l a b ∈ S) (a b : Fin n) : l.adjugate a b ∈ S := by
  let lR : Matrix (Fin n) (Fin n) S := fun a b => ⟨l a b, hl a b⟩
  have h1 : lR.map S.subtype = l := by ext a b; rfl
  have h2 := congrFun (congrFun (RingHom.map_adjugate S.subtype lR) a) b
  rw [← h1, show lR.map S.subtype = S.subtype.mapMatrix lR from rfl, ← h2]
  exact (lR.adjugate a b).2

theorem congr_dvd {p : PlF D} {y : (D.s.atP p).Ep} {c c' r : 𝓞 D.host.F} (hc : c = c' * r)
    (h : ∃ o ∈ (D.s.atP p).O, y =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) :
    ∃ o ∈ (D.s.atP p).O, y =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c')) * o := by
  obtain ⟨o, ho, rfl⟩ := h
  refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F r)) * o,
    Subring.mul_mem _ (alg_mem_O (fun q => D.s.atP q) p (iotaF_int_mem (fun q => D.s.atP q) p r)) ho, ?_⟩
  rw [hc, map_mul, map_mul, map_mul, mul_assoc]

theorem exist_of (hA : ∀ p, Agree δ M p) (hTy : ∀ p, (M p).split ≠ none → LocRealAt M δ u u' p) :
    Exist M δ u u' := by
  intro w' _ x hx
  have hLR : ∀ p, LocRealAt M δ u u' p := fun p => by
    by_cases h : (M p).split = none
    · exact locRealAt_ord u u' hA p h
    · exact hTy p h
  have hloc := fun p => hLR p w' (x.1 p) (hx p)
  choose Lp Up cp hcp0 hLp hUp hreal using hloc
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA ∅
  have hBad := Filter.eventually_cofinite.1 hgood
  set S : Finset (PlF D) := x.2.toFinset ∪ hBad.toFinset with hS
  set c : 𝓞 D.host.F := ∏ p ∈ S, cp p with hcdef
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hcp0 p
  obtain ⟨L, hL1, hL0, hLS, hLO⟩ := approx_lo (fun q => D.s.atP q) S c hc0 (fun p => Lp p)
    (fun p _ a => (hLp p).1 a) (fun p _ a b hab => (hLp p).2 a b hab)
  obtain ⟨U, hU1, hU0, hUS, hUO⟩ := approx_up (fun q => D.s.atP q) S c hc0 (fun p => Up p)
    (fun p _ a => (hUp p).1 a) (fun p _ a b hab => (hUp p).2 b a hab)
  have hLlo : IsLo L := ⟨hL1, hL0⟩
  have hUup : IsUp U := ⟨hU1, fun a b hab => hU0 b a hab⟩
  have hZ : (L * ptMat w' * U * Sg D.host.E D.R.rS) * Sg D.host.E D.R.rS = L * ptMat w' * U := by
    rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  refine ⟨L * ptMat w' * U * Sg D.host.E D.R.rS, ⟨L, U, fun i j => ⟨hL0 i j, fun h => h ▸ hL1 i⟩,
    fun i j => ⟨hU0 i j, fun h => h ▸ hU1 i⟩, by rw [zhatOM_eq]; exact hZ⟩, ?_⟩
  funext p
  by_cases hp : p ∈ S
  · have hsplit : c = cp p * ∏ q ∈ S.erase p, cp q := (Finset.mul_prod_erase S cp hp).symm
    exact hreal p L U hLlo hUup (fun a b => congr_dvd hsplit (hLS p hp a b))
      (fun a b => congr_dvd hsplit (hUS p hp a b))
  · have hpx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w' := by
      by_contra h
      exact hp (Finset.mem_union_left _ (x.2.mem_toFinset.2 h))
    have hpg : (M p).split = none ∧ (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
        ((D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧
          (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) ∧
        ∀ t ∈ (∅ : Finset D.host.E), ∀ k : Fin 3, t + ((k : ℕ) : D.host.E) ≠ 0 →
          (D.s.atP p).ιE (t + ((k : ℕ) : D.host.E)) ∈ (D.s.atP p).O ∧
            (D.s.atP p).ιE ((t + ((k : ℕ) : D.host.E))⁻¹) ∈ (D.s.atP p).O := by
      by_contra h
      exact hp (Finset.mem_union_right _ (hBad.mem_toFinset.2 h))
    have hentL : ∀ a b, (D.s.atP p).ιE (L a b) ∈ (D.s.atP p).O := hLO p hp
    have hentU : ∀ a b, (D.s.atP p).ιE (U a b) ∈ (D.s.atP p).O := hUO p hp
    have hLd : L.det = 1 := det_lo' hLlo
    have hUd : U.det = 1 := det_up' hUup
    have hinv : ∀ (X : PairVal.MatR D), X.det = 1 → (∀ a b, (D.s.atP p).ιE (X a b) ∈ (D.s.atP p).O) →
        ∀ a b, (D.s.atP p).ιE (X⁻¹ a b) ∈ (D.s.atP p).O := by
      intro X hX hXe a b
      rw [Matrix.inv_def, hX, Ring.inverse_one, one_smul]
      have h2 := congrFun (congrFun (RingHom.map_adjugate (D.s.atP p).ιE X) a) b
      rw [show ((D.s.atP p).ιE.mapMatrix X.adjugate) a b = (D.s.atP p).ιE (X.adjugate a b) from rfl] at h2
      rw [h2]
      exact adj_mem (D.s.atP p).O (fun a b => hXe a b) a b
    rw [hpx]
    exact tupZ_eq_x0L_at hA u u' hLlo hUup hZ p hpg.1 hpg.2.1.1 hpg.2.1.2 hpg.2.2.1.1 hpg.2.2.1.2
      (fun a b => ⟨hentL a b, hentU a b, hinv L hLd hentL a b, hinv U hUd hentU a b⟩)

end Assembly

end Formalism.L2.SG.Pf.PCountEx
