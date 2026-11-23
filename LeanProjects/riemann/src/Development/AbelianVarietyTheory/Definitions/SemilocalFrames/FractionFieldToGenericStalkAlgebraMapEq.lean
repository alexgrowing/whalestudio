import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsHaarSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer

noncomputable section
open ValuativeRel IsDedekindDomain NumberField ComplexConjugate Formalism.MainNotions.S.Loc
open scoped Classical

namespace GlobalTheory.SgGlob

structure ModFam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (g₁ g₂ : ℕ) where
  rank : Module.finrank F E = 2
  g₁_prime : g₁.Prime
  g₂_prime : g₂.Prime
  g_ne : g₁ ≠ g₂
  A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p
  M : ∀ p, Model (A p).Fp (A p).Ep
  ok : ∀ p, (M p).OK
  de : ∀ p, (A p).Fp
  de_ne : ∀ p, de p ≠ 0
  de_gen : ∀ p (x : (A p).Fp), (haveI := (A p).ellPrime;
    ∀ y ∈ 𝒪[(A p).Fp], ‖Algebra.trace ℚ_[resChar p] (A p).Fp (x * y)‖ ≤ 1) ↔ de p * x ∈ 𝒪[(A p).Fp]
  cj_eq : ∀ p, (M p).L.cj = (A p).cj
  fractionFieldToGenericStalk_algebraMap_eq : ∀ p y, (M p).L.psi0 y = (A p).psiE (-(algebraMap (A p).Fp (A p).Ep (de p)⁻¹ * y))
  typed : ∀ p, (M p).split.isSome ↔ (resChar p = g₁ ∨ resChar p = g₂)
  split_eq : ∀ p (G : SplitG (M p).L), (M p).split = some G →
    (G.q : (A p).Fp) = (resChar p : (A p).Fp) ∧ ∃ S, (A p).split = some S ∧ S.e = G.e

section Inhabitant

theorem exists_modFam {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) {g₁ g₂ : ℕ} (h₁ : g₁.Prime) (h₂ : g₂.Prime) (hne : g₁ ≠ g₂)
    (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E hc.sig p)
    (hA : ∀ p, (A p).split.isSome ↔ (resChar p = g₁ ∨ resChar p = g₂)) :
    ∃ X : ModFam F E hc.sig g₁ g₂, X.A = A := by
  choose θ t n h using fun p => LocModel.exists_isUnitGen hc (A p)
  choose M de h1 h2 h3 h4 h5 h6 h7 using fun p => LocModel.exists_model (A p) (h p)
  exact ⟨⟨hc.deg2, h₁, h₂, hne, A, M, h1, de, h2, h3, h4, h5, fun p => (h6 p).trans (hA p), h7⟩, rfl⟩

theorem nonempty_modFam {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) {g₁ g₂ : ℕ} (h₁ : g₁.Prime) (h₂ : g₂.Prime) (hne : g₁ ≠ g₂)
    (s₁ : ((Ideal.span {(g₁ : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    (s₂ : ((Ideal.span {(g₂ : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E) :
    Nonempty (ModFam F E hc.sig g₁ g₂) := by
  have hs : hc.sig ≠ AlgHom.id F E := by
    intro h
    have hs : Function.Surjective (algebraMap F E) := fun a => (hc.fixed a).1 (DFunLike.congr_fun h a)
    have h1 : Module.finrank F E = 1 :=
      (LinearEquiv.ofBijective (Algebra.linearMap F E)
        ⟨(algebraMap F E).injective, hs⟩).finrank_eq.symm.trans (Module.finrank_self F)
    have := hc.deg2
    omega
  have h : ∀ p : HeightOneSpectrum (𝓞 F), ∃ A : LocAt F E hc.sig p,
      (A.split.isSome ↔ (resChar p = g₁ ∨ resChar p = g₂)) := by
    intro p
    obtain ⟨L, hL⟩ := GlobalTheory.LocalData.exists_locAt F E hc.sig hc.deg2 p
    by_cases hp : resChar p = g₁ ∨ resChar p = g₂
    · obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt F E hc.sig hc.deg2 hs p L (by
        rcases hp with e | e <;> rw [e] <;> assumption)
      exact ⟨{ L with split := some S }, by simp [hp]⟩
    · exact ⟨L, by simp [hL, hp]⟩
  choose A hA using h
  obtain ⟨X, -⟩ := exists_modFam hc h₁ h₂ hne A hA
  exact ⟨X⟩

theorem exists_field_modFam : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E)
    (_ : StarRing E) (_ : Algebra F E) (hc : Formalism.BasicNotions.CMData F E) (g₁ g₂ : ℕ),
    Nonempty (ModFam F E hc.sig g₁ g₂) := by
  obtain ⟨A⟩ := Formalism.MainNotions.Inhab.arith_nonempty 0 (4 * (2 * 0 + 15) * 9 + 1)
  let H := Formalism.MainNotions.Inhab.hostOf A 0 0 0
  have hq : H.q.Prime := H.hyp.1
  have hd : H.d.Prime := H.hyp.2.1
  have hM : 1 < H.QS * H.q * H.d :=
    lt_of_lt_of_le hd.one_lt (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos hq.pos))
  obtain ⟨g₁, -, h₁, m₁⟩ := Formalism.MainNotions.Inhab.exists_one_mod _ 0 (by omega : H.QS * H.q * H.d ≠ 0)
  obtain ⟨g₂, l₂, h₂, m₂⟩ := Formalism.MainNotions.Inhab.exists_one_mod _ g₁ (by omega : H.QS * H.q * H.d ≠ 0)
  have hs : ∀ g : ℕ, g.Prime → g ≡ 1 [MOD H.QS * H.q * H.d] →
      ((Ideal.span {(g : ℤ)}).primesOver (𝓞 H.E)).ncard = Module.finrank ℚ H.E := fun g hg m => by
    rw [← GlobalTheory.HostSplit.ncard_placesOver H.E hg]
    exact (GlobalTheory.HostSplit.split_of_one_mod _ H g hg (Eq.trans m (Nat.mod_eq_of_lt hM))).1
  exact ⟨H.F, H.E, _, _, _, _, H.cmStar, _, GlobalTheory.Mem.host_cmData _ H, g₁, g₂,
    @nonempty_modFam _ _ _ _ _ _ H.cmStar _ _ _ _ h₁ h₂ l₂.ne (hs _ h₁ m₁) (hs _ h₂ m₂)⟩

end Inhabitant

section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def tau0 (M : Model F E) (T T' : F) : E :=
  match M.split with
  | none => 0
  | some G => G.e.symm (-T / (G.q : F), T' / (G.q : F))

def dLoc (M : Model F E) (τ : E) {n : ℕ} (w : Pt E n) : ℂ :=
  match w.blocks.getLast? with
  | none => 1
  | some b => if (b.2 : ℕ) = 2 then M.psiR (τ * ((b.1⁻¹ : Eˣ) : E)) else 1

def LastOne {r : ℕ} (w : Pt E (r + 1)) : Prop := ∃ x : Pt E r × Eˣ, w.blocks = x.1.blocks ++ [(x.2, 1)]

def KtopLoc (M : Model F E) (τ : E) {r : ℕ} (w w' : Pt E (r + 1)) : ℂ :=
  if h : LastOne w then
    (if h' : LastOne w' then
      (if h.choose.2 = h'.choose.2 then M.CuspSpanExtension ((h.choose.2 : E) - τ) h.choose.1 h'.choose.1 else 0)
    else 0)
  else if LastOne w' then 0 else dLoc M τ w * M.Kk (r + 1) w w' * conj (dLoc M τ w')

omit [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in

theorem lastOne_iff {r : ℕ} (w : Pt E (r + 1)) : LastOne w ↔ ∃ l t, w.blocks = l ++ [(t, 1)] := by
  refine ⟨fun ⟨x, hx⟩ => ⟨_, _, hx⟩, fun ⟨l, t, h⟩ => ⟨(⟨l, ?_⟩, t), h⟩⟩
  have := w.size
  rw [h] at this
  simpa using this

theorem KtopLoc_last_one (M : Model F E) (τ : E) {r : ℕ} {w w' : Pt E (r + 1)} {h h' : Pt E r} {t t' : Eˣ}
    (hw : w.blocks = h.blocks ++ [(t, 1)]) (hw' : w'.blocks = h'.blocks ++ [(t', 1)]) :
    KtopLoc M τ w w' = if t = t' then M.CuspSpanExtension ((t : E) - τ) h h' else 0 := by
  have key : ∀ {w : Pt E (r + 1)} {h : Pt E r} {t : Eˣ} (_ : w.blocks = h.blocks ++ [(t, 1)]) (H : LastOne w),
      H.choose = (h, t) := by
    intro w h t hw H
    have e := hw.symm.trans H.choose_spec
    have e1 := List.append_inj_left' e rfl
    have e2 := List.append_inj_right' e rfl
    refine Prod.ext ?_ (by simpa using e2.symm)
    generalize H.choose.1 = k at e1
    cases h; cases k; simpa using e1.symm
  have H : LastOne w := ⟨(h, t), hw⟩
  have H' : LastOne w' := ⟨(h', t'), hw'⟩
  unfold KtopLoc
  rw [dif_pos H, dif_pos H', key hw H, key hw' H']

theorem KtopLoc_mixed (M : Model F E) (τ : E) {r : ℕ} {w w' : Pt E (r + 1)} (h : ¬ (LastOne w ↔ LastOne w')) :
    KtopLoc M τ w w' = 0 := by
  unfold KtopLoc
  by_cases H : LastOne w <;> by_cases H' : LastOne w' <;> simp_all

theorem KtopLoc_not_last_one (M : Model F E) (τ : E) {r : ℕ} {w w' : Pt E (r + 1)} (h : ¬ LastOne w)
    (h' : ¬ LastOne w') : KtopLoc M τ w w' = dLoc M τ w * M.Kk (r + 1) w w' * conj (dLoc M τ w') := by
  unfold KtopLoc
  rw [dif_neg h, if_neg h']
end Local

namespace ModFam
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {g₁ g₂ : ℕ} (X : ModFam F E sig g₁ g₂)

def uP (p : HeightOneSpectrum (𝓞 F)) : ℚ :=
  (if resChar p = g₁ ∨ resChar p = g₂ then (resChar p : ℚ) else 1) / ((g₁ : ℚ) * g₂)

def cP (p : HeightOneSpectrum (𝓞 F)) : (X.A p).Fp := X.de p * ((uP (F := F) (g₁ := g₁) (g₂ := g₂) p : ℚ) : (X.A p).Fp)

def tmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : E) : (X.A p).Ep :=
  match (X.M p).split with
  | none => algebraMap (X.A p).Fp (X.A p).Ep (X.cP p ^ (-ν)) * (X.A p).ιE t
  | some G => G.e.symm (X.cP p ^ (-ν) * (G.e ((X.A p).ιE t)).1 / (G.q : (X.A p).Fp),
      (-1) ^ s * X.cP p ^ (-ν) * (G.e ((X.A p).ιE t)).2 / (G.q : (X.A p).Fp))

include X in

theorem exists_unitAt_eq_inv (p : HeightOneSpectrum (𝓞 F)) :
    ∃ m : ℕ, ¬ resChar p ∣ m ∧ uP (F := F) (g₁ := g₁) (g₂ := g₂) p = (m : ℚ)⁻¹ ∧
      g₁ * g₂ = (if resChar p = g₁ ∨ resChar p = g₂ then resChar p else 1) * m := by
  have h1 : (g₁ : ℚ) ≠ 0 := by exact_mod_cast X.g₁_prime.ne_zero
  have h2 : (g₂ : ℚ) ≠ 0 := by exact_mod_cast X.g₂_prime.ne_zero
  have hp : (resChar p).Prime := (X.A p).ellPrime.out
  unfold uP
  by_cases e1 : resChar p = g₁
  · refine ⟨g₂, fun h => X.g_ne (e1 ▸ (Nat.prime_dvd_prime_iff_eq hp X.g₂_prime).1 h), ?_, by simp [e1]⟩
    rw [if_pos (Or.inl e1), e1]; field_simp
  by_cases e2 : resChar p = g₂
  · refine ⟨g₁, fun h => e1 ((Nat.prime_dvd_prime_iff_eq hp X.g₁_prime).1 h), ?_, by simp [e2, mul_comm]⟩
    rw [if_pos (Or.inr e2), e2]; field_simp
  refine ⟨g₁ * g₂, fun h => ?_, by simp [e1, e2], by simp [e1, e2]⟩
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact e1 ((Nat.prime_dvd_prime_iff_eq hp X.g₁_prime).1 h)
  · exact e2 ((Nat.prime_dvd_prime_iff_eq hp X.g₂_prime).1 h)

theorem cP_ne_zero (p : HeightOneSpectrum (𝓞 F)) : X.cP p ≠ 0 := by
  haveI := (X.A p).char0
  obtain ⟨m, hm, e, -⟩ := X.exists_unitAt_eq_inv p
  have : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  unfold cP
  rw [e]
  exact mul_ne_zero (X.de_ne p) (by simpa using this)

def xmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (x : E) : (X.A p).Ep :=
  match (X.M p).split with
  | none => algebraMap (X.A p).Fp (X.A p).Ep (X.cP p ^ ν) * (X.A p).ιE x
  | some G => G.e.symm (X.cP p ^ ν * (G.e ((X.A p).ιE x)).1 * (G.q : (X.A p).Fp),
      (-1) ^ s * X.cP p ^ ν * (G.e ((X.A p).ιE x)).2 * (G.q : (X.A p).Fp))

def tfac (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) : (X.A p).Ep := X.tmod ν s p 1

theorem tmod_eq (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : E) :
    X.tmod ν s p t = X.tfac ν s p * (X.A p).ιE t := by
  unfold tfac tmod
  cases (X.M p).split with
  | none => simp
  | some G => apply G.e.injective; ext <;> simp <;> ring

theorem xmod_eq (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (x : E) :
    X.xmod ν s p x = X.xmod ν s p 1 * (X.A p).ιE x := by
  unfold xmod
  cases (X.M p).split with
  | none => simp
  | some G => apply G.e.injective; ext <;> simp <;> ring

theorem tfac_mul (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) : X.tfac ν s p * X.xmod ν s p 1 = 1 := by
  have hc : X.cP p ^ ν ≠ 0 := zpow_ne_zero _ (X.cP_ne_zero p)
  unfold tfac tmod xmod
  cases (X.M p).split with
  | none => simp only [map_one, mul_one]; rw [← map_mul, zpow_neg, inv_mul_cancel₀ hc, map_one]
  | some G =>
    have hq : (G.q : (X.A p).Fp) ≠ 0 := fun e => G.q_irr.ne_zero (Subtype.ext e)
    have hs : ((-1 : (X.A p).Fp) ^ s) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    apply G.e.injective
    ext
    · simp only [map_one, map_mul, AlgEquiv.apply_symm_apply, Prod.fst_mul, Prod.fst_one, zpow_neg]
      field_simp
    · simp only [map_one, map_mul, AlgEquiv.apply_symm_apply, Prod.snd_mul, Prod.snd_one, zpow_neg]
      field_simp
      exact hs

theorem tmod_mul_xmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) {t : E} (ht : t ≠ 0) :
    X.tmod ν s p t * X.xmod ν s p t⁻¹ = 1 := by
  rw [tmod_eq, xmod_eq, mul_mul_mul_comm, tfac_mul, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]

theorem isUnit_tmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : Eˣ) : IsUnit (X.tmod ν s p t) :=
  IsUnit.of_mul_eq_one _ (X.tmod_mul_xmod ν s p t.ne_zero)

theorem tmod_add (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t t' : E) :
    X.tmod ν s p (t + t') = X.tmod ν s p t + X.tmod ν s p t' := by
  simp only [tmod_eq, map_add, mul_add]

theorem tmod_sub (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t t' : E) :
    X.tmod ν s p (t - t') = X.tmod ν s p t - X.tmod ν s p t' := by
  simp only [tmod_eq, map_sub, mul_sub]

@[simp] theorem tmod_zero (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) : X.tmod ν s p 0 = 0 := by
  simp [tmod_eq]

theorem xmod_sub (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (x x' : E) :
    X.xmod ν s p (x - x') = X.xmod ν s p x - X.xmod ν s p x' := by
  rw [xmod_eq, X.xmod_eq ν s p x, X.xmod_eq ν s p x', map_sub, mul_sub]

theorem tmod_injective (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) : Function.Injective (X.tmod ν s p) := by
  haveI : Nontrivial (X.A p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (X.A p).Fp) (by rw [(X.A p).rank]; norm_num)
  intro t t' h
  rw [tmod_eq, tmod_eq] at h
  exact (X.A p).ιE.injective ((IsUnit.of_mul_eq_one _ (X.tfac_mul ν s p)).mul_left_cancel h)

def tmodU (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : Eˣ) : (X.A p).Epˣ :=
  if h : IsUnit (X.tmod ν s p t) then h.unit else 1

@[simp] theorem coe_tmodU (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : Eˣ) :
    ((X.tmodU ν s p t : (X.A p).Epˣ) : (X.A p).Ep) = X.tmod ν s p t := by
  unfold tmodU
  rw [dif_pos (X.isUnit_tmod ν s p t), IsUnit.unit_spec]

theorem coe_tmodU_inv (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : Eˣ) :
    (((X.tmodU ν s p t)⁻¹ : (X.A p).Epˣ) : (X.A p).Ep) = X.xmod ν s p (t : E)⁻¹ :=
  Units.inv_eq_of_mul_eq_one_right (by rw [coe_tmodU]; exact X.tmod_mul_xmod ν s p t.ne_zero)

theorem tmodU_injective (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) : Function.Injective (X.tmodU ν s p) := by
  intro t t' h
  apply Units.ext
  apply X.tmod_injective ν s p
  rw [← coe_tmodU, ← coe_tmodU, h]

def nu (r a s : ℕ) : ℤ := 2 * (r : ℤ) + 1 - 2 * a - s

def off (l : List (Eˣ × ℕ+)) (n : ℕ) : ℕ := ((l.take n).map fun b => (b.2 : ℕ)).sum

def blocksMod (r : ℕ) (p : HeightOneSpectrum (𝓞 F)) (l : List (Eˣ × ℕ+)) : List ((X.A p).Epˣ × ℕ+) :=
  l.mapIdx fun n b => (X.tmodU (nu r (off l n) b.2) b.2 p b.1, b.2)

lemma blocksMod_size (r : ℕ) (p : HeightOneSpectrum (𝓞 F)) (l : List (Eˣ × ℕ+)) :
    (X.blocksMod r p l).map (fun b => (b.2 : ℕ)) = l.map (fun b => (b.2 : ℕ)) := by
  apply List.ext_getElem <;> simp [blocksMod]

theorem blocksMod_concat (r : ℕ) (p : HeightOneSpectrum (𝓞 F)) (l : List (Eˣ × ℕ+)) (b : Eˣ × ℕ+) :
    X.blocksMod r p (l ++ [b]) = X.blocksMod r p l ++
      [(X.tmodU (nu r (l.map fun c => (c.2 : ℕ)).sum b.2) b.2 p b.1, b.2)] := by
  unfold blocksMod
  rw [List.mapIdx_concat]
  congr 1
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    have hi : i ≤ l.length := by simp at h1; omega
    have : off (l ++ [b]) i = off l i := by unfold off; rw [List.take_append_of_le_length hi]
    simp [this]
  · simp [off]

def ptMod (r : ℕ) (p : HeightOneSpectrum (𝓞 F)) {n : ℕ} (w : Pt E n) : Pt (X.A p).Ep n :=
  ⟨X.blocksMod r p w.blocks, by rw [X.blocksMod_size]; exact w.size⟩

theorem ptMod_snoc (r : ℕ) (p : HeightOneSpectrum (𝓞 F)) {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    X.ptMod r p (h.snoc t s) = (X.ptMod r p h).snoc (X.tmodU (nu r m s) s p t) s := by
  simp only [ptMod, Pt.snoc, blocksMod_concat, h.size]

theorem lastOne_ptMod (r : ℕ) (p : HeightOneSpectrum (𝓞 F)) {n : ℕ} (w : Pt E (n + 1)) :
    LastOne (X.ptMod r p w) ↔ LastOne w := by
  rw [lastOne_iff, lastOne_iff]
  constructor
  · rintro ⟨l, t, h⟩
    rcases List.eq_nil_or_concat w.blocks with e | ⟨l', b, e⟩
    · have := w.size
      simp [e] at this
    · rw [List.concat_eq_append] at e
      change X.blocksMod r p w.blocks = _ at h
      rw [e, blocksMod_concat] at h
      have h2 := List.append_inj_right' h rfl
      have h3 : b.2 = 1 := by simpa using (congrArg (List.map Prod.snd) h2)
      exact ⟨l', b.1, by rw [e, ← h3]⟩
  · rintro ⟨l, t, h⟩
    exact ⟨_, _, (congrArg (X.blocksMod r p) h).trans (X.blocksMod_concat r p l (t, 1))⟩

def La (ν : ℤ) (s : ℕ) : Set E := {t | ∀ p, X.tmod ν s p t ∈ (X.M p).R}

def LaSub (ν : ℤ) (s : ℕ) : AddSubgroup E :=
  AddSubgroup.ofSub (X.La ν s) ⟨0, fun p => by simp⟩ fun t ht t' ht' p => by
    rw [← sub_eq_add_neg, tmod_sub]; exact sub_mem (ht p) (ht' p)

@[simp] theorem coe_LaSub (ν : ℤ) (s : ℕ) : (X.LaSub ν s : Set E) = X.La ν s := rfl

def La' (ν : ℤ) (s : ℕ) : Set E := {x | ∀ p, X.xmod ν s p x ∈ (X.M p).R}

theorem inv_sub_inv_mem_La' (ν : ℤ) (s : ℕ) (t t' : Eˣ) : (t : E)⁻¹ - (t' : E)⁻¹ ∈ X.La' ν s ↔
    ∀ p, (((X.tmodU ν s p t)⁻¹ : (X.A p).Epˣ) : (X.A p).Ep) - (((X.tmodU ν s p t')⁻¹ : (X.A p).Epˣ) : (X.A p).Ep)
      ∈ (X.M p).R := by
  simp only [La', Set.mem_setOf_eq, coe_tmodU_inv, xmod_sub]

def Kglob (r i : ℕ) (w w' : Pt E i) : ℂ := ∏ᶠ p, (X.M p).Kk i (X.ptMod r p w) (X.ptMod r p w')

def Nglob (r : ℕ) {m : ℕ} (s : ℕ+) (t t' : Eˣ) (h h' : Pt E m) : ℂ :=
  ∏ᶠ p, (X.M p).Ns s (X.tmodU (nu r m s) s p t) (X.tmodU (nu r m s) s p t') (X.ptMod r p h) (X.ptMod r p h')

def Ktop (r : ℕ) (T T' : F) (w w' : Pt E (r + 1)) : ℂ :=
  if ∃ p, KtopLoc (X.M p) (tau0 (X.M p) ((X.A p).ιF T) ((X.A p).ιF T')) (X.ptMod r p w) (X.ptMod r p w') = 0 then 0
  else ∏ᶠ p, KtopLoc (X.M p) (tau0 (X.M p) ((X.A p).ιF T) ((X.A p).ιF T')) (X.ptMod r p w) (X.ptMod r p w')

omit X in

theorem nonempty_place : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩⟩

theorem Ktop_mixed (r : ℕ) (T T' : F) {w w' : Pt E (r + 1)} (h : ¬ (LastOne w ↔ LastOne w')) :
    X.Ktop r T T' w w' = 0 := by
  obtain ⟨p⟩ := nonempty_place (F := F)
  exact if_pos ⟨p, KtopLoc_mixed _ _ (by rwa [lastOne_ptMod, lastOne_ptMod])⟩

theorem KtopLoc_ptMod_last_one (r : ℕ) (p : HeightOneSpectrum (𝓞 F)) (τ : (X.A p).Ep) {w w' : Pt E (r + 1)}
    {h h' : Pt E r} {t t' : Eˣ} (hw : w.blocks = h.blocks ++ [(t, 1)]) (hw' : w'.blocks = h'.blocks ++ [(t', 1)]) :
    KtopLoc (X.M p) τ (X.ptMod r p w) (X.ptMod r p w') =
      if t = t' then (X.M p).CuspSpanExtension (X.tmod (nu r r 1) 1 p t - τ) (X.ptMod r p h) (X.ptMod r p h') else 0 := by
  have key : ∀ {w : Pt E (r + 1)} {h : Pt E r} {t : Eˣ}, w.blocks = h.blocks ++ [(t, 1)] →
      (X.ptMod r p w).blocks = (X.ptMod r p h).blocks ++ [(X.tmodU (nu r r 1) 1 p t, 1)] := by
    intro w h t hw
    change X.blocksMod r p w.blocks = _
    rw [hw, blocksMod_concat, h.size]
    rfl
  rw [KtopLoc_last_one _ _ (key hw) (key hw'), coe_tmodU]
  simp only [(X.tmodU_injective _ _ p).eq_iff]

theorem Ktop_of_ne (r : ℕ) (T T' : F) {w w' : Pt E (r + 1)} {h h' : Pt E r} {t t' : Eˣ}
    (hw : w.blocks = h.blocks ++ [(t, 1)]) (hw' : w'.blocks = h'.blocks ++ [(t', 1)]) (hne : t ≠ t') :
    X.Ktop r T T' w w' = 0 := by
  obtain ⟨p⟩ := nonempty_place (F := F)
  exact if_pos ⟨p, by rw [X.KtopLoc_ptMod_last_one r p _ hw hw', if_neg hne]⟩

theorem Ktop_eq_finprod (r : ℕ) (T T' : F) (w w' : Pt E (r + 1))
    (h : (Function.mulSupport fun p => KtopLoc (X.M p) (tau0 (X.M p) ((X.A p).ιF T) ((X.A p).ιF T'))
      (X.ptMod r p w) (X.ptMod r p w')).Finite) : X.Ktop r T T' w w' =
    ∏ᶠ p, KtopLoc (X.M p) (tau0 (X.M p) ((X.A p).ιF T) ((X.A p).ιF T')) (X.ptMod r p w) (X.ptMod r p w') := by
  unfold Ktop
  split_ifs with H
  · obtain ⟨p, hp⟩ := H
    exact (finprod_eq_zero _ p hp h).symm
  · rfl

def Nt (ν : ℤ) (s : ℕ) (t : E) : ℝ := if t = 0 then 0 else ∏ᶠ p, ((X.M p).modK (X.tmod ν s p t))⁻¹

@[simp] theorem Nt_zero (ν : ℤ) (s : ℕ) : X.Nt ν s 0 = 0 := if_pos rfl

theorem Nt_of_ne (ν : ℤ) (s : ℕ) {t : E} (ht : t ≠ 0) :
    X.Nt ν s t = ∏ᶠ p, ((X.M p).modK (X.tmod ν s p t))⁻¹ := if_neg ht

def Ndet (r : ℕ) {m : ℕ} (h : Pt E m) : ℝ := ∏ᶠ p, ((X.M p).detMod (X.ptMod r p h))⁻¹

def phi (r : ℕ) {i : ℕ} (w : Pt E i) : ℝ :=
  (w.blocks.mapIdx fun n b => X.Nt (nu r (off w.blocks n) b.2) b.2 b.1 ^
    ((b.2 : ℕ) * (2 * (i - (off w.blocks n + b.2)) + b.2 - 1) / 2)).prod

def KA (r i : ℕ) (w w' : Pt E i) : ℂ := X.Kglob r i w w' / ((X.phi r w * X.phi r w' : ℝ) : ℂ)

def KAtop (r : ℕ) (T T' : F) (w w' : Pt E (r + 1)) : ℂ :=
  X.Ktop r T T' w w' / ((X.phi r w * X.phi r w' : ℝ) : ℂ)

end ModFam

def lead {K : Type} [CommRing K] {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (l : ℕ) (hl : l ≤ n) : K :=
  (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def GZ {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {r : ℕ} (T T' : F)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E :=
  Z.det * sig Z.det - algebraMap F E (T * T') * (lead Z r (Nat.le_succ r) * sig (lead Z r (Nat.le_succ r)))

def psiInf {E : Type} [Field E] [NumberField E] (x : E) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ))

def ModFam.LaDual {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {g₁ g₂ : ℕ} (X : ModFam F E sig g₁ g₂) (ν : ℤ) (s : ℕ) : Set E :=
  {l | ∀ t ∈ X.La ν s, psiInf (l * t / ((g₁ * g₂ : ℕ) : E)) = 1}

example (r : ℕ) : ModFam.nu r r 1 = 0 := by simp [ModFam.nu]

example (r a s : ℕ) : ModFam.nu r a s = 2 * r + 3 - 2 * ((a : ℤ) + 1) - s := by unfold ModFam.nu; ring

example {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) (T T' : F) (z : E) :
    GZ (r := 0) sig T T' !![z] = z * sig z - algebraMap F E (T * T') := by
  simp [GZ, lead]

example : psiInf (1 / 4 : ℚ) = Complex.I := by
  unfold psiInf
  rw [Subsingleton.elim (DivisionRing.toRatAlgebra : Algebra ℚ ℚ) (Algebra.id ℚ), Algebra.trace_self_apply]
  refine Eq.trans ?_ Complex.exp_pi_div_two_mul_I
  congr 1
  push_cast
  ring

end GlobalTheory.SgGlob
