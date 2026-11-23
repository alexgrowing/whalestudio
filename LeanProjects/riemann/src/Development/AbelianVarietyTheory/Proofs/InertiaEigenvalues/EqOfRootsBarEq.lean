import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSeriesVectorMulOfParahoricBlockCharVectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.SerLocal

variable (D : D7)

theorem inePol_zero (w : PlE D.host) (s) (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (D.naut.lpZero w) s = 1 := by
  rw [((D.naut.unr_iff_ine _).1 (D.naut.lpZero_unr w)).2 s hs, D.naut.lpDim_zero, pow_zero]

theorem inePol_foldr {ι : Type} {w : PlE D.host} (F : ι → D.naut.LP w) (l : List ι) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (l.foldr (fun x acc => D.naut.lpSum (F x) acc) (D.naut.lpZero _)) s =
      (l.map fun x => D.naut.inePol (F x) s).prod := by
  induction l with
  | nil => simpa using inePol_zero D w s hs
  | cons x l ih => rw [List.foldr_cons, D.naut.inePol_sum, ih, List.map_cons, List.prod_cons]

theorem inePol_speh (p : Part D.naut.CG) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (spehLoc D.nd D.naut p w) s = D.naut.inePol (D.naut.locG p.π w) s ^ p.d := by
  have e : spehLoc D.nd D.naut p w = (List.range p.d).foldr (fun (j : ℕ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - j)) acc) (D.naut.lpZero w) := by
    simp only [spehLoc, bind_pure_comp, List.map_eq_map, List.foldr_map]
  rw [e, inePol_foldr D (fun k : ℕ => D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) _ s hs]
  simp [D.naut.inePol_tw _ _ s hs]

theorem inePol_iso (P : List (Part D.naut.CG)) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut P w) s =
      (P.map fun p => D.naut.inePol (D.naut.locG p.π w) s ^ p.d).prod := by
  rw [isoLoc, inePol_foldr D (fun p => spehLoc D.nd D.naut p w) _ s hs]
  simp only [inePol_speh D _ w s hs]

theorem inePol_twist (hU : IneUnr D) (i : D.nd.Loc) (Sig : List (Part D.naut.CG)) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut
      (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w) s =
      D.naut.inePol (isoLoc D.nd D.naut Sig w) s * D.naut.inePol (D.naut.locG (D.naut.muC i) w) s ^ D.R.t := by
  rw [inePol_iso D _ w s hs, inePol_iso D _ w s hs, twistIso, List.map_map]
  have e : ∀ {a} (π : D.naut.CG a), D.naut.inePol (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) s =
      D.naut.inePol (D.naut.locG π w) s := fun π => by
    rw [D.naut.locG_tw]
    exact hU w _ _ (D.naut.locG_dim _ w) (D.naut.etaTinv_def w).1 s hs
  simp [Function.comp_def, e, muPart]

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem eq_of_rootsBar_eq {f f' : (ZMod g)[X]} (hf : f.Monic) (hf' : f'.Monic)
    (h : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar f') : f = f' := by
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (f'.map _)).eq_prod_roots_of_monic (hf'.map _)]
  exact congrArg (fun m => (Multiset.map (fun x => X - C x) m).prod) h

theorem rootsBar_pow (c : ZMod g) (t : ℕ) :
    Formalism.CyclotomicNorms.rootsBar ((X - C c) ^ t) = t • {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c} := by
  rw [Formalism.CyclotomicNorms.rootsBar, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, roots_pow, roots_X_sub_C]

theorem eq_of_teich (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (hτ : Function.Injective τ) {f f' : (ZMod g)[X]} (hf : f.Monic)
    (hf' : f'.Monic) (c : ZMod g) (t : ℕ)
    (h : ((Formalism.CyclotomicNorms.rootsBar (f * (X - C c) ^ t)).map fun x => X - C (τ x)).prod =
      ((Formalism.CyclotomicNorms.rootsBar f').map fun x => X - C (τ x)).prod *
        (X - C (τ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c))) ^ t) : f = f' := by
  have h0 : f * (X - C c) ^ t ≠ 0 := (hf.mul ((monic_X_sub_C c).pow t)).ne_zero
  have hm : Formalism.CyclotomicNorms.rootsBar (f * (X - C c) ^ t) = Formalism.CyclotomicNorms.rootsBar f + Formalism.CyclotomicNorms.rootsBar ((X - C c) ^ t) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.map_mul, roots_mul]
    rw [← Polynomial.map_mul]
    exact Polynomial.map_ne_zero h0
  rw [hm, rootsBar_pow, Multiset.map_add, Multiset.prod_add, Multiset.map_nsmul, Multiset.prod_nsmul,
    Multiset.map_singleton, Multiset.prod_singleton] at h
  have h2 := mul_right_cancel₀ (pow_ne_zero t (X_sub_C_ne_zero _)) h
  have h3 := congrArg Polynomial.roots h2
  have e : ∀ m : Multiset (Formalism.CyclotomicNorms.Fbar g),
      ((m.map fun x => X - C (τ x)).prod).roots = m.map τ := fun m => by
    rw [← roots_multiset_prod_X_sub_C (m.map τ), Multiset.map_map]; rfl
  rw [e, e] at h3
  exact eq_of_rootsBar_eq hf hf' (Multiset.map_injective hτ h3)

end Roots

theorem serLoc : ∀ (D : D7) (S : ∀ k, @Sys (D.host.g k) ⟨D.host.g_prime k⟩),
    (∀ k f, D.ntypes.eSer k f = @Sys.e _ ⟨D.host.g_prime k⟩ (S k) D.R.r f) → IneUnr D → LocType D S →
    SerLoc D := by
  intro D S hS hU hL i σ' k v f F hF hne
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hex : ∃ P Sig, (∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) ∧
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) ∧
      ∃ F' ∈ D.naut.typeV i P,
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f)) F' ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hne
    rw [D.mtpar_tie i σ'] at hF
    have hle : (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) ∧
        IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv)},
        D.naut.typeV i P) ≤
        LinearMap.ker (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f))) :=
      iSup₂_le fun P ⟨Sig, h1, h2⟩ F' hF' => hno P Sig h1 h2 F' hF'
    exact hle hF
  obtain ⟨P, Sig, hSig, hBC, F', hF', hne'⟩ := hex
  obtain ⟨π, χ, c, h1, h2, h3, h4⟩ := hL i P k v
  obtain ⟨u, hu, hu'⟩ := h1 F' hF' (D.ntypes.eSer k f)
    (Subalgebra.mem_center_iff.2 fun b => (D.ntypes.eSer_central k f b).symm) hne'
  rw [hS] at hu'
  have hmon : f.Monic := ((S k).label D.R.r f (fun h0 => hu' (by rw [h0]; simp [actTop]))).1
  have hHas := GlobalTheory.T.hasSeriesVector_mul_of_parahoricBlockCharVector _ (S k) _ _ π.ρ D.R.r D.R.t χ _ f u rfl h2 hu hu'
  have h5 := h4 _ hHas
  have hs := D.ntypes.tg_mem k v
  rw [← hBC.2.2.2.1 _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v), inePol_twist D hU i Sig _ _ hs, hSig, h3,
    D.ntypes.inertiaCharpoly_type k v _ (by
      rw [← D.ntypes.labPar_def, (D.ntypes.labPar_monic k σ' v).2, D.ntypes.locPar_dim]),
    ← D.ntypes.labPar_def] at h5
  exact eq_of_teich _ (GlobalTheory.TameLabels.teich_injective _ (D.ntypes.teichC_inj k)) hmon (D.ntypes.labPar_monic k σ' v).1 c _ h5.symm

end GlobalTheory.SerLocal
