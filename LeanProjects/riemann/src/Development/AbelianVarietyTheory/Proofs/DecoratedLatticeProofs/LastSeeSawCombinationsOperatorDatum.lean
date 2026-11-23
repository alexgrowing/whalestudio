import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastOpPf

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

theorem cA_mem_idAt {P : Pl D → Prop} {a : AE D} (h : a ∈ idAt D P) : cA D a ∈ idAt D P := by
  obtain ⟨ε, -, hc, -, hε, -⟩ := (localComponents D P).1
  rw [hε] at h ⊢
  conv_rhs => rw [← h]
  rw [map_mul, hc]

theorem mxAt_adj {P : Pl D → Prop} {m n : ℕ} {x : Mx D m n} (hx : MxAt P x) : MxAt P (adj x) := fun i j => by
  have := cA_mem_idAt (hx j i)
  simpa [adj] using this

theorem mxAt_mul_l {P : Pl D → Prop} {l m n : ℕ} (A : Mx D l m) {x : Mx D m n} (hx : MxAt P x) : MxAt P (A * x) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hx k j)

theorem mxAt_mul_r {P : Pl D → Prop} {l m n : ℕ} {x : Mx D l m} (hx : MxAt P x) (A : Mx D m n) : MxAt P (x * A) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hx i k)

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (c : AE D) {x : Mx D m n} (hx : MxAt P x) : MxAt P (c • x) :=
  fun i j => Ideal.mul_mem_left _ _ (hx i j)

theorem mxAt_add {P : Pl D → Prop} {m n : ℕ} {x y : Mx D m n} (hx : MxAt P x) (hy : MxAt P y) : MxAt P (x + y) :=
  fun i j => add_mem (hx i j) (hy i j)

theorem mxAt_zero {P : Pl D → Prop} {m n : ℕ} : MxAt P (0 : Mx D m n) := fun _ _ => zero_mem _

theorem combAt_single {P : Pl D → Prop} {S T : HSp D} {z : WO S T} (hz : MxAt P z) (c : ℂ) :
    CombAt P (Finsupp.single z c) := fun u hu => by
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]; exact hz

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ z ∈ c.support, c z * heisO ψ S T z f w := by
  simp [comb, Finset.sum_apply, smul_eq_mul]

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (z : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single z c) f = c • heisO ψ S T z f := by
  by_cases hc : c = 0
  · subst hc; simp [comb]
  · simp [comb, Finsupp.support_single_ne_zero _ hc]

theorem symplOH_zero_right (S T : HSp D) (w : WO S T) : symplOH S T w 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem ofAdj_starAdj (S T : HSp D) (x : WO S T) : ofAdj S T (starAdj S T x) = x := by
  have h : incA D (-D.host.xi0⁻¹) * cA D (incA D D.host.xi0) = 1 := by
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, ← map_mul]
    rw [show -D.host.xi0⁻¹ * -D.host.xi0 = 1 by rw [neg_mul_neg]; exact inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]
    exact map_one _
  rw [ofAdj, starAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h,
    one_smul, Matrix.mul_assoc, Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

def invLine {m n : ℕ} (τ : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E := fun i j => (τ j i)⁻¹

theorem mul_invLine {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (hL : L.rank = 1) (hL'' : L''.rank = 1)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) : τ * invLine τ = 1 := by
  have hsub : ∀ a b : Fin L.rank, a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  have hsub'' : ∀ a b : Fin L''.rank, a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  let k0 : Fin L''.rank := ⟨0, by omega⟩
  have hne : ∀ i, τ i k0 ≠ 0 := by
    intro i hi
    have h0 : τ = 0 := by
      funext a b
      rw [hsub a i, hsub'' b k0]; exact hi
    rw [h0, Matrix.mul_zero, Matrix.mul_zero] at hτ
    have hc : (-(D.host.xi0 * star D.host.xi0)) ≠ 0 := by
      have := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
      simpa using this
    have hg : L''.gram = 0 := by
      have := hτ.symm
      rwa [smul_eq_zero, or_iff_right hc] at this
    haveI : Nonempty (Fin L''.rank) := ⟨k0⟩
    exact Formalism.L2.Theta.gram_det_ne L'' (by rw [hg, Matrix.det_zero])
  funext i j
  rw [hsub j i, Matrix.one_apply_eq, Matrix.mul_apply, Finset.sum_eq_single k0 (fun b _ hb => absurd (hsub'' b k0) hb)
    (fun h => absurd (Finset.mem_univ _) h)]
  show τ i k0 * (τ i k0)⁻¹ = 1
  exact mul_inv_cancel₀ (hne i)

def kapInv {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (b : WO L S) : WO S L'' :=
  (rat (invLine τ) : Mx D L''.rank L.rank) * starAdj L S b

theorem kap_kapInv {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (hL : L.rank = 1) (hL'' : L''.rank = 1)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) (b : WO L S) :
    kap τ S (kapInv τ S b) = b := by
  rw [kap, kapInv, ← Matrix.mul_assoc, ← rat_mul, mul_invLine τ hL hL'' hτ, rat_one, Matrix.one_mul, ofAdj_starAdj]

theorem mxAt_kapInv {P : Pl D → Prop} {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D)
    {b : WO L S} (hb : MxAt P b) : MxAt P (kapInv τ S b) :=
  mxAt_mul_l _ (mxAt_smul _ (mxAt_mul_l _ (mxAt_mul_r (mxAt_adj hb) _)))

theorem mxAt_kap {P : Pl D → Prop} {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D)
    {w : WO S L''} (hw : MxAt P w) : MxAt P (kap τ S w) :=
  mxAt_smul _ (mxAt_mul_l _ (mxAt_mul_r (mxAt_adj (mxAt_mul_l _ hw)) _))

theorem kap_add {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (w w' : WO S L'') :
    kap τ S (w + w') = kap τ S w + kap τ S w' := by
  rw [kap, kap, kap, ← GlobalTheory.LinkKappa.ofAdj_add, Matrix.mul_add]

theorem symplOH_kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) (w w' : WO S L'') :
    symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w' := by
  have hτ' : τᴴ * (L.gram * τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; congr 1; push_cast; ring
  have h := GlobalTheory.LinkKappa.symplO_ofAdj L L'' S τ (-1) hτ' w w'
  unfold symplOH
  rw [kap, kap, h]
  push_cast; ring

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem lastBi_apply {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (u : WO A S) (v : WO S X) :
    lastBi o o'' τ Ξ Φ₂ u v = Φ₂ (o''.resT S v).1 * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := rfl

theorem heisO_split {V₀ A L S L'' : HSp D} (o : OrthDec V₀ A L) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (ψ : AddChar (AF D.host.F) ℂ)
    (Ξ : WO V₀ S → ℂ) (x u : WO A S) (y w : WO S L'') :
    heisO ψ V₀ S ((o.resS S).symm (x, kap τ S y)) Ξ ((o.resS S).symm (u, kap τ S w)) =
      ψ (symplOH A S u x) * ψ (symplOH S L'' w y) * Ξ ((o.resS S).symm (u + x, kap τ S (w + y))) := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← map_add, Prod.mk_add_mk, kap_add,
    symplOH_kap τ hτ, AddChar.map_add_eq_mul]

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem biComb_lastBi {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (ψ : AddChar (AF D.host.F) ℂ)
    (d : WO A S →₀ ℂ) (d' : WO S X →₀ ℂ) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) :
    biComb ψ A S X d d' (lastBi o o'' τ Ξ Φ₂) = ∑ p ∈ d.support ×ˢ d'.support,
      lastBi o o'' τ (comb ψ V₀ S (Finsupp.single ((o.resS S).symm (p.1, kap τ S (o''.resT S p.2).2)) (d p.1 * d' p.2)) Ξ)
        (comb ψ S T (Finsupp.single (o''.resT S p.2).1 1) Φ₂) := by
  funext u v
  simp only [Finset.sum_apply, lastBi_apply, comb_single, Pi.smul_apply, smul_eq_mul, one_mul, heisO_split o τ hτ]
  simp only [biComb, comb_apply]
  simp only [heisO, lastBi_apply, map_add, Prod.fst_add, Prod.snd_add, o''.symplOH_resT, AddChar.map_add_eq_mul]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem lastBi_comb {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (hL : L.rank = 1) (hL'' : L''.rank = 1)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (ψ : AddChar (AF D.host.F) ℂ)
    (e : WO V₀ S →₀ ℂ) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) :
    lastBi o o'' τ (comb ψ V₀ S e Ξ) Φ₂ = ∑ z ∈ e.support, biComb ψ A S X (Finsupp.single (o.resS S z).1 (e z))
      (Finsupp.single ((o''.resT S).symm (0, kapInv τ S (o.resS S z).2)) 1) (lastBi o o'' τ Ξ Φ₂) := by
  funext u v
  simp only [Finset.sum_apply]
  rw [lastBi_apply, comb_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hz : (o.resS S).symm ((o.resS S z).1, kap τ S (kapInv τ S (o.resS S z).2)) = z := by
    rw [kap_kapInv τ hL hL'' hτ, Prod.mk.eta, AddEquiv.symm_apply_apply]
  have hK := heisO_split o τ hτ ψ Ξ (o.resS S z).1 u (kapInv τ S (o.resS S z).2) (o''.resT S v).2
  rw [hz] at hK
  rw [hK]
  simp only [biComb, comb_single, Pi.smul_apply, smul_eq_mul, one_mul, heisO, lastBi_apply, map_add,
    AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero, o''.symplOH_resT, symplOH_zero_right,
    AddChar.map_add_eq_mul, AddChar.map_zero_eq_one]
  ring

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem sum_equivFin {α M : Type} [AddCommMonoid M] (s : Finset α) (f : α → M) :
    ∑ p ∈ s, f p = ∑ i : Fin s.card, f (s.equivFin.symm i : α) :=
  (Finset.sum_coe_sort s f).symm.trans (Equiv.sum_comp s.equivFin.symm (fun p : s => f p)).symm

theorem lastOp : ∀ D : D7, GlobalTheory.FinPl.LastOp D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ P
  refine ⟨fun e he => ?_, fun d d' hd hd' => ?_⟩
  · refine ⟨⟨e.support.card, fun i => Finsupp.single (o.resS S (e.support.equivFin.symm i : WO V₀ S)).1
        (e (e.support.equivFin.symm i : WO V₀ S)), fun i => Finsupp.single ((o''.resT S).symm
        (0, kapInv τ S (o.resS S (e.support.equivFin.symm i : WO V₀ S)).2)) 1⟩, fun i => ⟨?_, ?_⟩, fun Ξ Φ₂ => ?_⟩
    · exact combAt_single (mxAt_mul_r (he _ (e.support.equivFin.symm i).2) _) _
    · refine combAt_single ?_ 1
      rw [OrthDec.resT_symm_apply]
      exact mxAt_add (mxAt_mul_l _ mxAt_zero) (mxAt_mul_l _ (mxAt_kapInv τ S (mxAt_mul_r (he _ (e.support.equivFin.symm i).2) _)))
    · rw [lastBi_comb o o'' τ hL hL'' hτ ψ e Ξ Φ₂, sum_equivFin]
      rfl
  · refine ⟨(d.support ×ˢ d'.support).card,
      fun i => Finsupp.single ((o.resS S).symm (((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).1,
        kap τ S (o''.resT S ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).2).2))
        (d ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).1 *
          d' ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).2),
      fun i => Finsupp.single (o''.resT S ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).2).1 1,
      fun i => ⟨?_, ?_⟩, fun Ξ Φ₂ => ?_⟩
    · have hp := Finset.mem_product.1 ((d.support ×ˢ d'.support).equivFin.symm i).2
      refine combAt_single ?_ _
      rw [OrthDec.resS_symm_apply]
      exact mxAt_add (mxAt_mul_r (hd _ hp.1) _) (mxAt_mul_r (mxAt_kap τ S (mxAt_mul_l _ (hd' _ hp.2))) _)
    · have hp := Finset.mem_product.1 ((d.support ×ˢ d'.support).equivFin.symm i).2
      exact combAt_single (mxAt_mul_l _ (hd' _ hp.2)) _
    · rw [biComb_lastBi o o'' τ hτ ψ d d' Ξ Φ₂, sum_equivFin]

end GlobalTheory.LastOpPf
