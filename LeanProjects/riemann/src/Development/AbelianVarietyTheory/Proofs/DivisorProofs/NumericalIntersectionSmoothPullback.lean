import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCalcNumOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationSymmetricFormIdentityStatement
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.ChernInv

open MvPolynomial

section Cls

variable {e : ℕ} (M : Man e) {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
  (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ))

def conjSub : AddSubgroup M.Fun where
  carrier := {g | M.Smooth g ∧
    ∀ σ σ', (Weight.ofFun (M.pull ε π g σ)).IsConj (Weight.ofFun (M.pull ε π g σ'))}
  add_mem' {g g'} hg hg' := ⟨(InhabCalc.smSub M).add_mem hg.1 hg'.1, fun σ σ' i y y' h hy =>
    congrArg₂ (· + ·) (hg.2 σ σ' i y y' h hy) (hg'.2 σ σ' i y y' h hy)⟩
  zero_mem' := ⟨(InhabCalc.smSub M).zero_mem, fun _ _ _ _ _ _ _ => rfl⟩
  neg_mem' {g} hg := ⟨(InhabCalc.smSub M).neg_mem hg.1, fun σ σ' i y y' h hy =>
    congrArg Neg.neg (hg.2 σ σ' i y y' h hy)⟩

variable {M ε π}

theorem icls_fnB_congr {a b : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (h : a = b) (ha hca hb hcb) :
    (fnB a ha hca).icls = (fnB b hb hcb).icls := by
  subst h
  rfl

variable (hsm : ∀ u, M.Smooth u → ∀ σ z, CxPts.CInfAt (M.pull ε π u σ) z)

def fnCls : conjSub M ε π →+ HermLB.IsomClass p :=
  AddMonoidHom.mk' (fun g => (fnB (M.pull ε π g) (hsm g g.2.1) g.2.2).icls) fun g g' => by
    rw [← HermLB.icls_tens]
    refine HermLB.icls_eq_iff.2 ?_
    refine ((HermLB.isometric_tens_fnB _ _ (hsm g' g'.2.1) g'.2.2).trans ?_).symm
    exact HermLB.isometric_of_chart id (fun _ => le_rfl) (fun _ _ _ _ _ => rfl) fun _ _ _ _ => rfl

end Cls

open HermLB in

theorem chernOn_of_numOn : GlobalTheory.Published.ArCalc → ∀ (e : ℕ) (M : Man e) (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (K : Calc M) (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (ν : ℝ) (ι : Type) [Fintype ι] (L : ι → HermLB p) (v : ι → K.V), IsArithVar p e → (∀ u, M.Smooth u → ∀ σ z, CxPts.CInfAt (M.pull ε π u σ) z) → K.NumOn ε π ν L v → ∀ u, M.Smooth u → ∀ hu hc (n : Option ι → ℤ) (f : M.Fun), M.Smooth f → (∀ σ σ', (Weight.ofFun (M.pull ε π f σ)).IsConj (Weight.ofFun (M.pull ε π f σ'))) → chInt (ArInt.comb (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu hc) L) n) e (M.pull ε π f) = ν * M.int (fun _ => K.c1 (∑ i, (n (some i) : ℝ) • v i + (n none : ℝ) • K.ar u)) f := by
  intro H e M k _ X _ p K ε π ν ι _ L v hX hsm hN u hus hu hc n f hf hfc
  classical
  let L' : Option ι → HermLB p := fun o => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu hc) L
  let G : Option (Option ι) → HermLB p := fun o => o.elim (fnB (M.pull ε π f) (hsm f hf) hfc) L'
  obtain ⟨Ψ, hΨ⟩ := ((H.arExists k X p e hX).2 (Option (Option ι)) G).1
  have hch := H.arChange k X p e hX (Option ι) L' (M.pull ε π f) (hsm f hf) hfc Ψ hΨ n
  let U : conjSub M ε π := ⟨(2 : ℝ) • u, (InhabCalc.smSub M).smul_mem 2 hus, hc⟩
  let F : conjSub M ε π := ⟨f, hf, hfc⟩
  let w := ∑ i, (n (some i) : ℝ) • v i + (n none : ℝ) • K.ar u
  have key : ∀ t : ℤ, Ψ ((C (t : ℝ) * MvPolynomial.X none + rename some (lin fun i => (n i : ℝ))) ^ (e + 1)) =
      ν * K.num (fun _ => w + (t : ℝ) • ((1 / 2 : ℝ) • K.ar f)) := by
    intro t
    let g : M.Fun := (n none : ℝ) • u + ((t : ℝ) / 2) • f
    have hg : M.Smooth g :=
      (InhabCalc.smSub M).add_mem ((InhabCalc.smSub M).smul_mem _ hus) ((InhabCalc.smSub M).smul_mem _ hf)
    let Gt : conjSub M ε π := t • F + n none • U
    have hGt : (Gt : M.Fun) = (2 : ℝ) • g := by
      simp only [Gt, g, U, F, AddSubgroup.coe_add, AddSubgroup.coe_zsmul]
      rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ]
      module
    have hut : ∀ σ z, CxPts.CInfAt (M.pull ε π ((2 : ℝ) • g) σ) z := hsm _ ((InhabCalc.smSub M).smul_mem 2 hg)
    have hct : ∀ σ σ', (Weight.ofFun (M.pull ε π ((2 : ℝ) • g) σ)).IsConj
        (Weight.ofFun (M.pull ε π ((2 : ℝ) • g) σ')) := hGt ▸ Gt.2.2
    let Ft : Option ι → HermLB p := fun o => o.elim (fnB (M.pull ε π ((2 : ℝ) • g)) hut hct) L
    let A : Option ι → Option (Option ι) → ℤ := fun j =>
      j.elim (fun o => o.elim t fun o' => o'.elim (n none) 0) fun i => Pi.single (some (some i)) 1
    have hiso : ∀ j, (comb G (A j)).Isometric (Ft j) := by
      rintro (_ | i)
      · refine icls_eq_iff.1 ?_
        rw [icls_comb]
        simp only [Fintype.sum_option, A, G, L', Option.elim, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
        have e1 : (fnB (M.pull ε π f) (hsm f hf) hfc).icls = fnCls hsm F := rfl
        have e2 : (fnB (M.pull ε π ((2 : ℝ) • u)) hu hc).icls = fnCls hsm U := rfl
        rw [e1, e2, ← map_zsmul, ← map_zsmul, ← map_add]
        exact icls_fnB_congr (congrArg (M.pull ε π) hGt) _ _ _ _
      · exact isometric_comb_single G (some (some i))
    have hΦ := ((H.arIso k X p e hX).2 _ G Ψ hΨ).2.2 (Option ι) Ft A hiso
    have hn := hN g hg hut hct _ hΦ (fun o => o.elim 1 fun i => (n (some i) : ℝ))
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, aeval_lin] at hn
    have hb : ∀ o, (∑ j : Option ι, (j.elim 1 fun i => (n (some i) : ℝ)) * (A j o : ℝ)) =
        o.elim (t : ℝ) fun o' => (n o' : ℝ) := by
      rintro (_ | _ | i) <;> simp [A, Fintype.sum_option, Pi.single_apply]
    have hlin : (lin fun o => ∑ j : Option ι, (j.elim 1 fun i => (n (some i) : ℝ)) * (A j o : ℝ)) =
        C (t : ℝ) * MvPolynomial.X none + rename some (lin fun i => (n i : ℝ)) := by
      rw [show (fun o => ∑ j : Option ι, (j.elim 1 fun i => (n (some i) : ℝ)) * (A j o : ℝ)) =
          fun o => o.elim (t : ℝ) fun o' => (n o' : ℝ) from funext hb]
      simp only [lin, Fintype.sum_option (α := Option ι), Option.elim, map_sum, map_mul, rename_C, rename_X]
    rw [hlin] at hn
    rw [hn, Calc.top]
    congr 2
    funext _
    simp only [g, w, Option.elim, map_add, map_smul]
    module
  have hA := GlobalTheory.T.polarization_symmetric_form_identity e Ψ (MvPolynomial.X none) (rename some (lin fun i => (n i : ℝ))) K.num K.symm ν w
    ((1 / 2 : ℝ) • K.ar f) key
  rw [K.num.cons_smul, K.num_ar f hf, smul_eq_mul] at hA
  rw [hA] at hch
  linear_combination (-2) * hch

end GlobalTheory.Mean4O.ChernInv
