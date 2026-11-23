import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R)

def etaZ (k : Fin 2) : GL (Fin R.r) (ZMod (H.g k)) →* ℤˣ :=
  (quadraticChar (ZMod (H.g k))).toUnitHom.comp Matrix.GeneralLinearGroup.det

theorem exists_etaZ (ht : THyp H) (k : Fin 2) : ∃ x, etaZ H k x = -1 := by
  have hc : ringChar (ZMod (H.g k)) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact (ht.jac k).1
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  have hr : 0 < R.r := Nat.pos_of_ne_zero (r_ne_zero R)
  let M : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g k)) :=
    Matrix.diagonal (Function.update (fun _ => 1) (⟨0, hr⟩ : Fin R.r) (a : ZMod (H.g k)))
  have hdet : M.det = a := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact a.ne_zero), Units.ext ?_⟩
  show quadraticChar (ZMod (H.g k)) (Matrix.det M) = -1
  rw [hdet, ha]

variable (K : Type) [Field K] [CharZero K]

def psiU (k : Fin 2) (v : Fin R.f) : GL (Fin R.r) (ZMod (H.g k)) →* Kˣ :=
  if v.1 ≠ 0 then (Units.map (Int.castRingHom K).toMonoidHom).comp (etaZ H k) else 1

variable (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)

def PsiU : G0g (ndG H Lb what₂ h) →* Kˣ :=
  ∏ kv : Ix (ndG H Lb what₂ h), (psiU H K kv.1 kv.2).comp (Pi.evalMonoidHom _ kv)

theorem PsiU_apply (g : G0g (ndG H Lb what₂ h)) :
    ((PsiU H K Lb what₂ h g : Kˣ) : K) = ∏ kv : Ix (ndG H Lb what₂ h), ((psiU H K kv.1 kv.2 (g kv) : Kˣ) : K) := by
  unfold PsiU
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  rfl

theorem monicOf_eq_iff {k : Fin 2} (f : (ZMod (H.g k))[X]) (hm : f.Monic) (hd : f.natDegree = R.r)
    (a : Fin R.r → ZMod (H.g k)) : Formalism.CyclotomicNorms.monicOf a = f ↔ a = fun i : Fin R.r => f.coeff i := by
  constructor
  · intro e
    funext i
    rw [← e, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]
  · intro e
    rw [e]
    exact Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f hm hd

theorem evS_eSum' {K : Type} [Field K] {I : Type} [Fintype I] [dI : DecidableEq I] {G : I → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {L : I → Type} [∀ i, Fintype (L i)] (E : ∀ i, L i → MonoidAlgebra K (G i))
    (S : (∀ i, L i) → Prop) (ψ : ∀ i, G i → K) (b : ∀ i, L i) (hb : S b)
    (h1 : ∀ i, evS (ψ i) (E i (b i)) = 1) (h0 : ∀ i l, l ≠ b i → evS (ψ i) (E i l) = 0) :
    evS (fun g : ∀ i, G i => ∏ i, ψ i (g i)) (@eSum K _ I _ G _ _ L _ dI E S) = 1 := by
  unfold eSum
  rw [evS_sum, Finset.sum_eq_single b]
  · rw [if_pos hb, evS_tens]
    exact Finset.prod_eq_one fun i _ => h1 i
  · intro a _ hab
    split_ifs
    · rw [evS_tens]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
      exact Finset.prod_eq_zero (Finset.mem_univ i) (h0 i _ hi)
    · exact evS_zero _
  · intro h; exact absurd (Finset.mem_univ _) h

omit [CharZero K] in

theorem evS_e0F {what₂ : Rows.Data R} (N : NData R H what₂)
    (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k))))
    (ψ : ∀ kv : Ix N, GL (Fin R.r) (ZMod (H.g kv.1)) → K) (f : ∀ k, N.PlG k → (ZMod (H.g k))[X]) (hf : GoodT N f)
    (hδ : ∀ (kv : Ix N) (p : (ZMod (H.g kv.1))[X]), evS (ψ kv) (es kv.1 p) = if p = f kv.1 kv.2 then 1 else 0) :
    evS (fun g : G0g N => ∏ kv, ψ kv (g kv)) (e0F N es) = 1 := by
  have hm : ∀ k v, Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (f k v).coeff i) = f k v := fun k v =>
    Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ ((hf k).1.1 v).1 ((hf k).1.1 v).2.1
  have hb : GoodT N (fun k v => Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (f k v).coeff i)) := by
    have : (fun k v => Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (f k v).coeff i)) = f :=
      funext fun k => funext fun v => hm k v
    rw [this]; exact hf
  have hd1 : ∀ kv : Ix N, evS (ψ kv) (es kv.1 (Formalism.CyclotomicNorms.monicOf fun i : Fin R.r => (f kv.1 kv.2).coeff i)) = 1 :=
    fun kv => by rw [hδ, if_pos (hm _ _)]
  have hd0 : ∀ (kv : Ix N) (a : Fin R.r → ZMod (H.g kv.1)), a ≠ (fun i : Fin R.r => (f kv.1 kv.2).coeff i) →
      evS (ψ kv) (es kv.1 (Formalism.CyclotomicNorms.monicOf a)) = 0 := fun kv a e => by
    rw [hδ, if_neg (fun e' => e ((monicOf_eq_iff H _ ((hf kv.1).1.1 kv.2).1 ((hf kv.1).1.1 kv.2).2.1 a).mp e'))]
  exact evS_eSum' (I := Ix N) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
    (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => es kv.1 (Formalism.CyclotomicNorms.monicOf a))
    (fun a => GoodT N fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ψ
    (fun kv => fun i : Fin R.r => (f kv.1 kv.2).coeff i) hb hd1 hd0

theorem evS_e0L (ht : THyp H) :
    evS (fun g => ((PsiU H K Lb what₂ h g : Kˣ) : K)) (e0L H Lb what₂ h K) = 1 := by
  have e : (fun g => ((PsiU H K Lb what₂ h g : Kˣ) : K)) =
      fun g : G0g (ndG H Lb what₂ h) => ∏ kv : Ix (ndG H Lb what₂ h), ((psiU H K kv.1 kv.2 (g kv) : Kˣ) : K) :=
    funext fun g => PsiU_apply H K Lb what₂ h g
  rw [e]
  refine evS_e0F H K (ndG H Lb what₂ h) (esL Lb K) (fun kv x => ((psiU H K kv.1 kv.2 x : Kˣ) : K)) (tupL Lb)
    (goodT_tupL H Lb what₂ h) ?_
  rintro ⟨k, v⟩ p
  have hv' : (v : Fin R.f).1 ≠ 0 ∨ (v : Fin R.f).1 = 0 := (em _).symm
  show evS (fun x => ((psiU H K k v x : Kˣ) : K)) (esZ K _ (Lb.fA k) (Lb.fB k) p) = if p = tupL Lb k v then 1 else 0
  rcases hv' with hv | hv
  · obtain ⟨x, hx⟩ := exists_etaZ H ht k
    have hψ : (fun y => ((psiU H K k v y : Kˣ) : K)) =
        ⇑((Units.coeHom K).comp ((Units.map (Int.castRingHom K).toMonoidHom).comp (etaZ H k))) := by
      funext y; unfold psiU; rw [if_pos hv]; rfl
    rw [hψ, evS_esZ_ne (Lb.ne k) _ x (by
      show (((etaZ H k x : ℤˣ) : ℤ) : K) ≠ 1
      rw [hx]; norm_num)]
    have ht' : tupL Lb k v = Lb.fA k := by unfold tupL; rw [if_pos (by simpa using hv)]
    rw [ht']
    split_ifs <;> rfl
  · have hψ : (fun y => ((psiU H K k v y : Kˣ) : K)) = fun _ => 1 := by
      funext y; unfold psiU; rw [if_neg (not_not.mpr hv)]; rfl
    rw [hψ, evS_esZ_one (Lb.ne k)]
    have ht' : tupL Lb k v = Lb.fB k := by unfold tupL; rw [if_neg (by simpa using hv)]
    rw [ht']
    split_ifs <;> rfl

variable (V : Type) [AddCommGroup V] [Module K V]

def actGL : G0g (ndG H Lb what₂ h) →* (V ≃ₗ[K] V) where
  toFun g := LinearEquiv.smulOfUnit (PsiU H K Lb what₂ h g)
  map_one' := by
    ext x
    show PsiU H K Lb what₂ h 1 • x = x
    rw [map_one, one_smul]
  map_mul' a b := by
    ext x
    show PsiU H K Lb what₂ h (a * b) • x = PsiU H K Lb what₂ h a • PsiU H K Lb what₂ h b • x
    rw [map_mul, mul_smul]

theorem lift_actGL (ht : THyp H) :
    MonoidAlgebra.lift K (Module.End K V) (G0g (ndG H Lb what₂ h))
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (actGL H K Lb what₂ h V)) (e0L H Lb what₂ h K) = 1 := by
  rw [lift_scalar ((Units.coeHom K).comp (PsiU H K Lb what₂ h)) _ (fun g => by ext x; rfl)]
  show evS (fun g => ((PsiU H K Lb what₂ h g : Kˣ) : K)) _ • (1 : Module.End K V) = 1
  rw [evS_e0L H K Lb what₂ h ht, one_smul]

end Formalism.BasicNotions.Examples₂.NZ
