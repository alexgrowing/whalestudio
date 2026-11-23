import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspDetBlocks

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.Whittaker

open GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic in

theorem exists_isGeneric_subrep {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (P : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (S : Subrepresentation (P.locRep w)) (hS : S.toSubmodule ≠ ⊥) :
    ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ IsGeneric ψ S.toRepresentation := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ v : P.V, Good ψ (a - 1) v.1.1 := fun v => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ v.1 (P.cusp _ v.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀S, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hv1 : v₀.1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w g₀
  have hrt : ∀ u (v : P.V) x, whit ψ (a - 1) (P.locRep w u v).1.1 x =
      whit ψ (a - 1) v.1.1 (x * finGL E a (locGL E a w u)) := fun u v x => whit_rt _ _ _ _
  let l : P.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) v.1.1 h
      map_add' := fun v v' => congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => congrFun (whit_smul (a - 1) c v.1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) v.1.1 h := fun _ => rfl
  have hne : l (P.locRep w gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ u ∈ unipB (w.adicCompletion E) (Fin a), ∀ v : P.V,
      l (P.locRep w u v) = (locPsi hψ w (superDiag u) : ℂ) * l v := fun u hu v => by
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
    obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3, superDiag_eq_sum_pairs]
    rfl
  have hcont : Continuous (locPsi hψ w) := by
    refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  have hne1 : locPsi hψ w ≠ 1 := fun h1 => by
    obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  refine ⟨locPsi hψ w, hcont, hne1, l ∘ₗ S.toSubmodule.subtype, fun e' => hne ?_, fun u hu v => ?_⟩
  · exact LinearMap.congr_fun e' ⟨_, S.apply_mem_toSubmodule gw hv₀S⟩
  · exact hlaw u hu v.1

end GlobalTheory.CuspDetBlocks

namespace GlobalTheory.CuspDetBlocks

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.Whittaker

theorem piTensor_detRep_mulSingle {k : Type} [Field k] {c : ℕ} (d : Fin c → ℕ) (χ : Fin c → kˣ →* ℂˣ) (a : Fin c)
    (u : GL (Fin (d a)) k) (hu : u ∈ unipB k (Fin (d a))) (v : PiTensorProduct ℂ fun _ : Fin c => ℂ) :
    piTensor (fun b => detRep (Fin (d b)) (χ b)) (Pi.mulSingle a u) v = v := by
  have hdet : ∀ b, Matrix.GeneralLinearGroup.det ((Pi.mulSingle a u : ∀ b, GL (Fin (d b)) k) b) = 1 := fun b => by
    by_cases hb : b = a
    · subst hb
      rw [Pi.mulSingle_eq_same]
      obtain ⟨h1, h2⟩ := (mem_unipB k).1 hu
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular (fun i j hij => h1 i j hij)]
      simp [h2]
    · rw [Pi.mulSingle_eq_of_ne hb, map_one]
  have : piTensor (fun b => detRep (Fin (d b)) (χ b)) (Pi.mulSingle a u) = LinearMap.id := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp [piTensor_tprod, detRep, ofChar_apply, hdet]
  rw [this]; rfl

theorem le_one_of_intertwining : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x x' : ℕ) (τ : GlobalTheory.CuspRep.CuspSub E (x + x'))
    (w : HeightOneSpectrum (𝓞 E)) (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ), GlobalTheory.Published.GenericityGL →
    GlobalTheory.SmGL.IsSmoothChar χ₁ → GlobalTheory.SmGL.IsSmoothChar χ₂ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Q : Representation ℂ (GL (Fin (x + x')) (w.adicCompletion E)) V),
      GlobalTheory.SmGL.IsSubquotient Q (GlobalTheory.SmGL.prod₂ (GlobalTheory.SmGL.detRep (Fin x) χ₁) (GlobalTheory.SmGL.detRep (Fin x') χ₂)) →
      ∀ f : Q.IntertwiningMap (τ.locRep w), f ≠ 0 → x ≤ 1 ∧ x' ≤ 1 := by
  intro E _ _ _ x x' τ w χ₁ χ₂ H h₁ h₂ V _ _ Q hQ f hf
  let S : Subrepresentation (τ.locRep w) := ⟨LinearMap.range f.toLinearMap, by
    rintro g _ ⟨v, rfl⟩
    exact ⟨Q g v, f.isIntertwining _ _ g v⟩⟩
  have hS : S.toSubmodule ≠ ⊥ := fun h => hf (by
    have h' := LinearMap.range_eq_bot.1 h
    ext1
    first | exact h' | exact LinearMap.congr_fun h' _)
  obtain ⟨ψ, hc, h1, hg⟩ := exists_isGeneric_subrep τ w S hS
  have hSQ : IsSubquotient S.toRepresentation Q :=
    .of_surjective ⟨f.toLinearMap.rangeRestrict, fun g =>
      LinearMap.ext fun v => Subtype.ext (f.isIntertwining _ _ g v)⟩ (LinearMap.surjective_rangeRestrict _)
  let d : Fin 2 → ℕ := ![x, x']
  let χ : Fin 2 → (w.adicCompletion E)ˣ →* ℂˣ := ![χ₁, χ₂]
  let π : ∀ a : Fin 2, Representation ℂ (GL (Fin (d a)) (w.adicCompletion E)) ℂ :=
    fun a => detRep (Fin (d a)) (χ a)
  have hd : ∑ a, d a = d 0 + d 1 := Fin.sum_univ_two d
  obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd hd π
  have hs : IsSubquotient S.toRepresentation (parInd (stdBlocks d hd) (piTensor π)) :=
    (hSQ.trans hQ).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => by
    fin_cases a
    exacts [h₁, h₂]
  have hρ : IsSmooth (piTensor π) :=
    isSmooth_piTensor fun a => (isSmooth_ofChar_iff _).2 (hχ a).detChar
  have hb := fun a => H.block_le_one hc h1 (stdBlocks d hd) hρ hs hg a
    (fun u hu v => piTensor_detRep_mulSingle d χ a u hu v)
  exact ⟨hb 0, hb 1⟩

end GlobalTheory.CuspDetBlocks
