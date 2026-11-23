import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.FunMv

open GlobalTheory.Mem.Dil GlobalTheory.Mem.Col2.DilPt

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_add {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c d : 𝓞 E ⧸ P.asIdeal}
    (ha : HasRes P a c) (hb : HasRes P b d) : HasRes P (a + b) (c + d) := by
  obtain ⟨r, rfl, hr⟩ := ha
  obtain ⟨r', rfl, hr'⟩ := hb
  refine ⟨r + r', by rw [map_add], ?_⟩
  have e : a + b - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r + r')) =
      (a - algebraMap E _ (algebraMap (𝓞 E) E r)) + (b - algebraMap E _ (algebraMap (𝓞 E) E r')) := by
    simp only [map_add]; ring
  rw [e]
  exact Valuation.map_add_lt _ hr hr'

theorem hasRes_mul {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c d : 𝓞 E ⧸ P.asIdeal}
    (ha : HasRes P a c) (hb : HasRes P b d) : HasRes P (a * b) (c * d) := by
  have hale := hasRes_le_one ha
  obtain ⟨r, rfl, hr⟩ := ha
  obtain ⟨r', rfl, hr'⟩ := hb
  refine ⟨r * r', by rw [map_mul], ?_⟩
  have e : a * b - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r * r')) =
      a * (b - algebraMap E _ (algebraMap (𝓞 E) E r')) + algebraMap E _ (algebraMap (𝓞 E) E r') * (a - algebraMap E _ (algebraMap (𝓞 E) E r)) := by
    simp only [map_mul]; ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hale) hr'
  · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one P r')) hr

theorem hasRes_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) (a : ι → P.adicCompletion E) (c : ι → 𝓞 E ⧸ P.asIdeal)
    (h : ∀ j ∈ s, HasRes P (a j) (c j)) : HasRes P (∑ j ∈ s, a j) (∑ j ∈ s, c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasRes_coe P 0
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact hasRes_add (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem exists_hasRes [StarRing E] {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} (hP : P.under (𝓞 F) = v)
    (x : E ⊗[F] v.adicCompletion F) (hx : Valued.v (psi v P hP x) ≤ 1) : ∃ c, HasRes P (psi v P hP x) c := by
  obtain ⟨z, rfl⟩ : ∃ z, prV (E := E) v z = x := ⟨_, Formalism.UG.P.afsplit_prV_IE v x⟩
  rw [psi_prV] at hx ⊢
  obtain ⟨c, hc⟩ := exists_res P z hx
  exact ⟨_, c, rfl, hc⟩

end Res

end GlobalTheory.Mem.Col2.FunMv

end

noncomputable section

namespace GlobalTheory.Mem.Col2.FunMv

open GlobalTheory.Mem.Dil GlobalTheory.Mem.Col2.DilPt
open scoped TensorProduct

theorem hasRes_last {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (y k : GL (Fin n) (AfE F E)) (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (hP : P.under (𝓞 F) = v)
    (x : Sp E n) (r : Fin n) (b : 𝓞 E ⧸ P.asIdeal) (cj : Fin n → 𝓞 E ⧸ P.asIdeal)
    (hk : ∀ j, HasRes P (adAt F P ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then b else 0))
    (hy : ∀ j, HasRes P (psi v P hP (prV (E := E) v (GlobalTheory.Mem.Col2.pullV y x j))) (cj j)) :
    HasRes P (adAt F P (GlobalTheory.Mem.Col2.pullV (y * k) x r)) (b * cj r) := by
  rw [pullbackVector_mul_right]
  have e1 : adAt F P ((((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV y x) r) =
      ∑ j, adAt F P ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j) * adAt F P (GlobalTheory.Mem.Col2.pullV y x j) := by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have e2 : b * cj r = ∑ j, (if j = r then b else 0) * cj j := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [e1, e2]
  refine hasRes_sum _ _ _ fun j _ => hasRes_mul (hk j) ?_
  rw [← psi_prV v P hP]
  exact hy j

end GlobalTheory.Mem.Col2.FunMv

end

noncomputable section

namespace GlobalTheory.Mem.Col2.FunMv

open GlobalTheory.Mem.Dil GlobalTheory.Mem.Col2.DilPt
open scoped TensorProduct

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {hc : Formalism.BasicNotions.CMData F E} {n T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {S : Formalism.L2.Forms.StepLevel F E hc.sig (1 : Matrix (Fin n) (Fin n) E) T f bad}
  {π : 𝓞 E} {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)}

def resL (hLb : IsBase S π) (hP : P.under (𝓞 F) = v) (h3 : π ∉ (conjPrime₂ P).asIdeal) (r : Fin n) :
    latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)) →+
      𝓞 E ⧸ P.asIdeal where
  toFun s := Classical.choose (exists_hasRes hP (s.1 r) (val_coord_le hLb hP h3 s.2 r))
  map_zero' := by
    have h := Classical.choose_spec (exists_hasRes hP ((0 : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))).1 r) (val_coord_le hLb hP h3 (zero_mem _) r))
    refine h.unique ?_
    have h0 := hasRes_coe P 0
    simpa using h0
  map_add' s t := by
    have hs := Classical.choose_spec (exists_hasRes hP (s.1 r) (val_coord_le hLb hP h3 s.2 r))
    have ht := Classical.choose_spec (exists_hasRes hP (t.1 r) (val_coord_le hLb hP h3 t.2 r))
    have hst := Classical.choose_spec (exists_hasRes hP ((s + t).1 r) (val_coord_le hLb hP h3 (s + t).2 r))
    refine hst.unique ?_
    have e : psi v P hP ((s + t).1 r) = psi v P hP (s.1 r) + psi v P hP (t.1 r) := by
      rw [← map_add]; rfl
    rw [e]
    exact hasRes_add hs ht

theorem resL_spec (hLb : IsBase S π) (hP : P.under (𝓞 F) = v) (h3 : π ∉ (conjPrime₂ P).asIdeal) (r : Fin n)
    (s : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))) :
    HasRes P (psi v P hP (s.1 r)) (resL hLb hP h3 r s) :=
  Classical.choose_spec (exists_hasRes hP (s.1 r) (val_coord_le hLb hP h3 s.2 r))

theorem exists_fun (hLb : IsBase S π) (hv : (T : 𝓞 F) ∈ v.asIdeal) (hP : P.under (𝓞 F) = v)
    (hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P)
    (h2 : π ∉ P.asIdeal ^ 2) (h3 : π ∉ (conjPrime₂ P).asIdeal)
    (hk : ∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)),
      t'.1 = Formalism.UG.inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0)
    (hT : T.Prime) (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = T) (r : Fin n) (hr : r.1 + 1 = n) :
    ∃ ι₀ : S.fM v hv →+ 𝓞 E ⧸ P.asIdeal, ∀ s c, HasRes P (psi v P hP (s.1 r)) c → ι₀ (S.fT v hv s) = c := by
  classical
  set ψ := resL hLb hP h3 r with hψ
  have hle : ∀ x, ψ x = 0 → S.fT v hv x = 0 := fun x hx => by
    have h := resL_spec hLb hP h3 r x
    rw [← hψ, hx] at h
    exact fT_kill hLb hv hP hw h2 h3 hk r hr x (hasRes_lt_one h)
  have hne : ∃ a, (S.fT v hv).toAddMonoidHom a ≠ 0 := by
    by_contra H
    push_neg at H
    exact S.fT_ne v hv (LinearMap.ext H)
  have hker : ∀ x, S.fT v hv x = 0 → ψ x = 0 := fun x hx =>
    GlobalTheory.Mem.Col2.Reside.ker_of_prime (S.fT v hv).toAddMonoidHom ψ (hcard ▸ hT) hne hle x hx
  have hsurj : Function.Surjective (S.fT v hv) := by
    haveI : Fact (Nat.card (S.fM v hv)).Prime := ⟨(S.fM_card v hv).symm ▸ hT⟩
    rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card (S.fT v hv).toAddMonoidHom.range with h | h
    · exfalso
      obtain ⟨a, ha⟩ := hne
      have : (S.fT v hv).toAddMonoidHom a ∈ (S.fT v hv).toAddMonoidHom.range := ⟨a, rfl⟩
      rw [h] at this
      exact ha this
    · intro m
      have : m ∈ (S.fT v hv).toAddMonoidHom.range := by rw [h]; trivial
      obtain ⟨a, ha⟩ := this
      exact ⟨a, ha⟩
  let g := Function.surjInv hsurj
  have hg : ∀ m, S.fT v hv (g m) = m := Function.surjInv_eq hsurj
  refine ⟨{ toFun := fun m => ψ (g m), map_zero' := ?_, map_add' := ?_ }, fun s c hc => ?_⟩
  · refine hker _ ?_
    rw [hg]
  · intro m m'
    rw [← sub_eq_zero, ← map_add, ← map_sub]
    refine hker _ ?_
    rw [map_sub, map_add, hg, hg, hg, sub_self]
  · show ψ (g (S.fT v hv s)) = c
    have e : ψ (g (S.fT v hv s)) = ψ s := by
      rw [← sub_eq_zero, ← map_sub]
      refine hker _ ?_
      rw [map_sub, hg, sub_self]
    rw [e]
    exact (resL_spec hLb hP h3 r s).unique hc

end Loc

end GlobalTheory.Mem.Col2.FunMv

end

noncomputable section

namespace GlobalTheory.Mem.Col2.FunMv

open GlobalTheory.Mem.Dil GlobalTheory.Mem.Col2.DilPt
open scoped TensorProduct

theorem exists_fun' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    (S : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad) (π : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hLb : ∀ x, x ∈ S.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (hP : P.under (𝓞 F) = v)
    (hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P)
    (h2 : π ∉ P.asIdeal ^ 2) (h3 : π ∉ (conjPrime₂ P).asIdeal)
    (hk : ∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb)),
      t'.1 = Formalism.UG.inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0)
    (hT : T.Prime) (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = T) (r : Fin n) (hr : r.1 + 1 = n) :
    ∃ ι₀ : S.fM v hv →+ 𝓞 E ⧸ P.asIdeal, (∀ s c, HasRes P (psi v P hP (s.1 r)) c → ι₀ (S.fT v hv s) = c) ∧
      ∀ (s : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb))) (j : Fin n),
        ∃ c, HasRes P (psi v P hP (s.1 j)) c := by
  subst hJ
  obtain ⟨ι₀, h⟩ := exists_fun (S := S) hLb hv hP hw h2 h3 hk hT hcard r hr
  exact ⟨ι₀, h, fun s j => exists_hasRes hP (s.1 j) (val_coord_le (S := S) hLb hP h3 s.2 j)⟩

end GlobalTheory.Mem.Col2.FunMv

end

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.Col2.TC.funMoved_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ β : Ch, FunKilled (K β).lev (X.piT u) → ∀ (P : (B.primes X).vT u) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ ι : (K β).lev.fM v h →+ 𝓞 B.fields.E ⧸ P.1.asIdeal, ∀ c, chOf c = β → GlobalTheory.TwU.FunMoved (sm I l Z) (K β).lev P v h ι ((K (chOf c)).y ⟨c, rfl⟩).1 ((I.stp u a i).rep c).1.1.deco.1 := by
  intro B X I hI hPins l Z u a i hi bad Ch chOf K k hR β hkill P v h hov
  classical
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hPr := l.pr
  have hgr := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hPins l Z).2.2.2 i hi).1
  have hsP : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := by
    ext x
    exact TwU.mem_seamP (sm I l Z) P.1 x
  rw [hsP] at hov
  have hPv : P.1.under (𝓞 B.host.F) = v := by
    unfold IsOver at hov
    exact HeightOneSpectrum.ext hov.symm
  have hw : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w.under (𝓞 B.host.F) = v → w = P.1 ∨ w = conjPrime₂ P.1 := fun w hw' =>
    (under_eq_iff B.host P.1 w).1 (hw'.trans hPv.symm)
  have hcard : Nat.card (𝓞 B.host.E ⧸ P.1.asIdeal) = B.T u := by
    have e := hPr.vT_norm u P.1 P.2
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at e
    exact e
  have hN : 0 < B.R.N i := B.R.N_pos i
  let r : Fin (B.R.N i) := ⟨B.R.N i - 1, by omega⟩
  have hr : r.1 + 1 = B.R.N i := by show B.R.N i - 1 + 1 = _; omega
  obtain ⟨ι₀, hι₀, hres⟩ := GlobalTheory.Mem.Col2.FunMv.exists_fun' B.sp.cm hgr (K β).lev (X.piT u) P.1 v (fun x => hR.lb β x) h hPv hw
    (hPr.piT_notMem_sq hX u P.2) (conj_piT_notMem hPr u P) (hkill v h) (hPr.T_prime u) hcard r hr
  refine ⟨(AddMonoidHom.mulLeft (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)))).comp ι₀, fun c hc => ?_⟩
  subst hc
  intro w hw' z hz
  choose cj hcj using hres z
  have hf := (hR.pt c).f P w hw' r hr
  have hsum := GlobalTheory.Mem.Col2.FunMv.hasRes_last (((K (chOf c)).y ⟨c, rfl⟩).1 : GA B (B.R.N i)) (k (chOf c)) v P.1 hPv w r _ cj (fun j => hR.k_T (chOf c) P r j hr)
    (fun j => by have := hcj j; rw [hz] at this; exact this)
  refine (hf.unique hsum).trans ?_
  show _ = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) * ι₀ ((K (chOf c)).lev.fT v h z)
  exact congrArg _ (hι₀ z (cj r) (hcj r)).symm
