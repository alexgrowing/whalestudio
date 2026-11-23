import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltrationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueLie

theorem exists_combo {k F : Type} [Field k] [CommRing F] {a : ℕ} (χ : Fin a → F →+* k)
    (hχ : Function.Injective χ) (v : Fin a → k) :
    ∃ (r : ℕ) (lam : Fin r → k) (c : Fin r → F), ∀ j, ∑ l, lam l * χ j (c l) = v j := by
  let g : F → (Fin a → k) := fun x j => χ j x
  have htop : Submodule.span k (Set.range g) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hφ0
    have hinj : Function.Injective (fun j => ((χ j : F →* k))) := by
      intro i j h
      apply hχ
      ext x
      exact DFunLike.congr_fun h x
    have hli := (linearIndependent_monoidHom F k).comp _ hinj
    have hsum : ∑ j, φ (Pi.single j 1) • (((χ j : F →* k)) : F → k) = 0 := by
      funext x
      have hx : φ (g x) = 0 := hle (Submodule.subset_span ⟨x, rfl⟩)
      rw [GlobalTheory.HTUniv.coord φ (g x)] at hx
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hx]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [g, mul_comm]
    have h0 := Fintype.linearIndependent_iff.1 hli _ hsum
    refine LinearMap.ext fun w => ?_
    rw [GlobalTheory.HTUniv.coord φ w]
    simp [h0]
  have hv : v ∈ Submodule.span k (Set.range g) := htop ▸ Submodule.mem_top
  obtain ⟨n, f, gg, hfg⟩ := Submodule.mem_span_set'.1 hv
  choose c hc using fun l => (gg l).2
  refine ⟨n, f, c, fun j => ?_⟩
  have := congrFun hfg j
  rw [Finset.sum_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, ← hc l, smul_eq_mul]

theorem injective_chars {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) {k : Type} [Field k] (β : R →+* k) :
    Function.Injective (fun i => β.comp (b.t i)) := by
  intro i j h
  by_contra hij
  have h1 := b.comax i j hij
  have h2 : Ideal.map β (Ideal.span (Set.range fun x => b.t i x - b.t j x)) = ⊥ := by
    rw [Ideal.map_span, Ideal.span_eq_bot]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have := RingHom.congr_fun h x
    simp only [RingHom.comp_apply] at this
    rw [map_sub, this, sub_self]
  rw [h1, Ideal.map_top] at h2
  exact (top_ne_bot : (⊤ : Ideal k) ≠ ⊥) h2

theorem root_sub_ne_zero {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) {k : Type} [Field k] (β : R →+* k) :
    β b.ρ - ((D.tr : k) - β b.ρ) ≠ 0 := by
  intro h0
  set z : ℤ := D.tr ^ 2 - 4 * D.nm with hz
  have hp : ¬ p ∣ z.natAbs := fun h => D.disc_p (Int.natCast_dvd.2 h)
  have hcop : z.natAbs.Coprime p := ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 hp).symm
  have hu : IsUnit ((z.natAbs : ℕ) : k) := by simpa using (b.unit _ hcop).map β
  have hroot : β b.ρ ^ 2 - (D.tr : k) * β b.ρ + (D.nm : k) = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  have hzk : (z : k) = 0 := by
    have e : (z : k) = (β b.ρ - ((D.tr : k) - β b.ρ)) ^ 2 -
        4 * (β b.ρ ^ 2 - (D.tr : k) * β b.ρ + (D.nm : k)) := by
      rw [hz]; push_cast; ring
    rw [e, h0, hroot]; ring
  have hsq : (((z.natAbs : ℤ) : k)) ^ 2 = 0 := by
    rw [← Int.cast_pow, Int.natAbs_sq, Int.cast_pow, hzk]; ring
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
  rw [Int.cast_natCast] at this
  exact hu.ne_zero this

end GlobalTheory.HTGlueLie

noncomputable section
namespace GlobalTheory.HTGlueLie
variable {k : Type} [Field k] {d : ℕ} (A₀ : Over (Sp k)) [GrpObj A₀]
abbrev CrysC (k : Type) [Field k] (d : ℕ) (A₀ : Over (Sp k)) [GrpObj A₀] : Type 1 :=
  Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀

theorem crdL_smul (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) (u : CrysC k d A₀) (r : k) (q : primDR A₀) :
    π (u ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (r • q))) = r • π (u ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull q)) := by
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul]

theorem crdL_add (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) (u : CrysC k d A₀) (q q' : primDR A₀) :
    π (u ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (q + q'))) = π (u ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull q)) + π (u ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull q')) := by
  simp only [map_add]

def crdL (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) (u : CrysC k d A₀) : primDR A₀ →ₗ[k] k where
  toFun q := π (u ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull q))
  map_add' q q' := crdL_add A₀ π u q q'
  map_smul' r q := crdL_smul A₀ π u r q

theorem crdL_apply (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) (u : CrysC k d A₀) (q : primDR A₀) :
    crdL A₀ π u q = π (u ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull q)) := rfl

theorem crdL_add_u (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) (u v : CrysC k d A₀) (q : primDR A₀) :
    crdL A₀ π (u + v) q = crdL A₀ π u q + crdL A₀ π v q := by
  simp only [crdL_apply, LinearMap.add_apply, map_add]

theorem crdL_zero_u (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) (q : primDR A₀) :
    crdL A₀ π 0 q = 0 := by
  simp only [crdL_apply, LinearMap.zero_apply, map_zero]

def crd (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) : CrysC k d A₀ →+ HdR A₀ where
  toFun u := crdL A₀ π u
  map_zero' := LinearMap.ext fun q => crdL_zero_u A₀ π q
  map_add' u v := LinearMap.ext fun q => crdL_add_u A₀ π u v q

theorem crd_apply (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) (u : CrysC k d A₀) (q : primDR A₀) :
    crd A₀ π u q = π (u ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull q)) := rfl

theorem crd_smul (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) (r : k) (u : CrysC k d A₀) :
    crd A₀ π (algebraMap k (TrivSqZeroExt k (Fin d → k)) r • u) = r • crd A₀ π u := by
  refine LinearMap.ext fun q => ?_
  have e : crd A₀ π (algebraMap k (TrivSqZeroExt k (Fin d → k)) r • u) q = r • crd A₀ π u q := by
    simp only [crd_apply, LinearMap.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul]
  rw [e, LinearMap.smul_apply]

theorem primPull_const_pull (g : A₀ ⟶ A₀) [IsMonHom g] (q : primDR A₀) :
    primPull (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) g
        ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull q) =
      (GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (primPull (dp0 k) (𝟙 _) g q) := by
  have K := (homMor (dp0 k) (𝟙 _) g).comp (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)
  have e1 := GrpMor.pull_pull (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)
    (homMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) g) K
    (fun _ ↦ rfl) (by simp) q
  have e2 := GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) g) (GlobalTheory.FODef.constMorV k (Fin d → k) A₀) K
    (fun _ ↦ rfl) rfl q
  exact e1.trans e2.symm

theorem crd_push (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) (g : A₀ ⟶ A₀) [IsMonHom g] (u : CrysC k d A₀) :
    crd A₀ π (push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) g u) =
      push (dp0 k) (𝟙 _) g (crd A₀ π u) := by
  refine LinearMap.ext fun q => ?_
  rw [crd_apply, push_apply, primPull_const_pull, push_apply, crd_apply]

theorem mem_glueFil_of_crd (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (u : CrysC k d A₀)
    (h0 : crd A₀ (TrivSqZeroExt.fstHom k k (Fin d → k)).toLinearMap u ∈ Fil A₀)
    (h1 : ∀ j, crd A₀ (LinearMap.proj j ∘ₗ TrivSqZeroExt.sndHom k (Fin d → k)) u -
      f j (crd A₀ (TrivSqZeroExt.fstHom k k (Fin d → k)).toLinearMap u) ∈ Fil A₀) :
    u ∈ GlobalTheory.HTGlue.glueFil A₀ f := by
  refine ⟨_, h0, _, h1, fun q => ?_⟩
  ext
  · simp only [crd_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    rfl
  · simp only [crd_apply, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
      LinearMap.add_apply, LinearMap.sub_apply, add_sub_cancel]
    rfl

theorem mem_glueFil_of_crd_mem (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (Z : Submodule k (HdR A₀)) (hZ : Z ≤ Fil A₀)
    (hf : ∀ j, ∀ x ∈ Z, f j x ∈ Fil A₀) (u : CrysC k d A₀)
    (hu : ∀ π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k, crd A₀ π u ∈ Z) :
    u ∈ GlobalTheory.HTGlue.glueFil A₀ f :=
  mem_glueFil_of_crd A₀ f u (hZ (hu _)) fun j => sub_mem (hZ (hu _)) (hf j _ (hu _))
end GlobalTheory.HTGlueLie

namespace GlobalTheory.HTGlueLie

section Lie

open GlobalTheory.HTCount

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R} (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k)

theorem sum_mem_lieZ {Idx : Type} [Fintype Idx] (lam : Idx → k) (c : Idx → 𝓞 D.F) {y : HdR o₀.A}
    (hy : y ∈ rhoPart o₀ β) (h : ∀ j, ∑ l, lam l * β (b.t j (c l)) = 0) :
    ∑ l, lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y ∈ lieZ o₀ β := by
  let e := Fintype.equivFin Idx
  apply Submodule.subset_span
  refine ⟨Fintype.card Idx, lam ∘ e.symm, c ∘ e.symm, y, hy, fun i => ?_, ?_⟩
  · rw [← h i]
    exact e.symm.sum_comp (fun l => lam l * β (b.t i (c l)))
  · exact (e.symm.sum_comp (fun l => lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y)).symm

theorem mul_sub_mem_lieZ {r : ℕ} (lam : Fin r → k) (c : Fin r → 𝓞 D.F) (i : Fin D.a)
    (hc : ∀ j, ∑ l, lam l * β (b.t j (c l)) = if i = j then 1 else 0) {y : HdR o₀.A}
    (hy : y ∈ rhoPart o₀ β) (c₀ : 𝓞 D.F) :
    crysAct o₀ (algebraMap (𝓞 D.F) D.O c₀) (∑ l, lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y) -
      β (b.t i c₀) • ∑ l, lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y ∈ lieZ o₀ β := by
  have H := sum_mem_lieZ o₀ β (Idx := Fin r ⊕ Fin r) (Sum.elim lam (fun l => -(β (b.t i c₀)) * lam l))
    (Sum.elim (fun l => c₀ * c l) c) hy (fun j => by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, map_mul]
      have h1 : ∑ l, lam l * (β (b.t j c₀) * β (b.t j (c l))) = β (b.t j c₀) * ∑ l, lam l * β (b.t j (c l)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
      have h2 : ∑ l, -(β (b.t i c₀)) * lam l * β (b.t j (c l)) = -(β (b.t i c₀)) * ∑ l, lam l * β (b.t j (c l)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
      rw [h1, h2, hc j]
      split_ifs with hij
      · subst hij; ring
      · ring)
  convert H using 1
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, map_sum, map_smul, map_mul, Module.End.mul_apply, Finset.smul_sum,
    smul_smul, sub_eq_add_neg, neg_mul, neg_smul, Finset.sum_neg_distrib]

theorem one_sub_mem_lieZ {r : Fin D.a → ℕ} (lam : ∀ i, Fin (r i) → k) (c : ∀ i, Fin (r i) → 𝓞 D.F)
    (hc : ∀ i j, ∑ l, lam i l * β (b.t j (c i l)) = if i = j then 1 else 0) {y : HdR o₀.A}
    (hy : y ∈ rhoPart o₀ β) :
    y - ∑ i, ∑ l, lam i l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c i l)) y ∈ lieZ o₀ β := by
  have H := sum_mem_lieZ o₀ β (Idx := Option (Σ i, Fin (r i)))
    (fun o => Option.elim o 1 (fun s => -lam s.1 s.2)) (fun o => Option.elim o 1 (fun s => c s.1 s.2)) hy
    (fun j => by
      rw [Fintype.sum_option, Fintype.sum_sigma]
      simp only [Option.elim_none, Option.elim_some, map_one, one_mul, neg_mul, Finset.sum_neg_distrib]
      rw [Finset.sum_congr rfl fun i _ => hc i j, Finset.sum_ite_eq']
      simp)
  convert H using 1
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [Option.elim_none, Option.elim_some, map_one, Module.End.one_apply, one_smul, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

theorem smul_mem_rhoPart (δ : k) (x : HdR o₀.A) :
    δ • (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) x - ((D.tr : k) - β b.ρ) • x) ∈ rhoPart o₀ β := by
  refine ⟨δ • x, ?_⟩
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_sub, smul_comm δ]

theorem lieZ_le_fil (hs : t = spMap β) : lieZ o₀ β ≤ Fil o₀.A := by
  have hF : ∀ (x : D.O) (v : HdR o₀.A), v ∈ Fil o₀.A → crysAct o₀ x v ∈ Fil o₀.A := fun x v hv => by
    haveI := o₀.act.hom x
    rw [crysAct_apply]
    exact push_mem_Fil _ hv
  refine Submodule.span_le.2 ?_
  rintro z ⟨r, lam, c, y, ⟨h, rfl⟩, hsum, rfl⟩
  set A := crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω)
  have hq0 : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hq := congrArg (fun x => crysAct o₀ (algebraMap (𝓞 D.F) D.O x) h) hq0
  simp only [map_add, map_sub, map_mul, map_intCast, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.intCast_apply, LinearMap.zero_apply] at hq
  rw [← Int.cast_smul_eq_zsmul k, ← Int.cast_smul_eq_zsmul k] at hq
  have hroot : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k) := by
    have := congrArg β b.ρ_root
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    linear_combination -this
  have hy0 : crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) ((A - ((D.tr : k) - β b.ρ) • 1) h) -
      β b.ρ • ((A - ((D.tr : k) - β b.ρ) • 1) h) ∈ Fil o₀.A := by
    have e : crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) ((A - ((D.tr : k) - β b.ρ) • 1) h) -
        β b.ρ • ((A - ((D.tr : k) - β b.ρ) • 1) h) = 0 := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
      linear_combination (norm := module) hq + hroot • h
    rw [e]; exact zero_mem _
  obtain ⟨w, hw, hws⟩ := GlobalTheory.T.harrisTaylor_lie_condition_mod_hodgeFiltration p D R b N k β t hs o₀ _ hy0
  set y := (A - ((D.tr : k) - β b.ρ) • 1) h
  have e : ∑ l, lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y =
      ∑ l, lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) (y - ∑ i, w i) +
        ∑ i, ∑ l, lam l • (crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) (w i) - β (b.t i (c l)) • w i) := by
    have h3 : ∀ i, ∑ l, lam l • β (b.t i (c l)) • w i = 0 := fun i => by
      simp only [smul_smul, ← Finset.sum_smul, hsum i, zero_smul]
    simp only [map_sub, map_sum, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, h3, sub_zero]
    rw [Finset.sum_comm (f := fun i l => lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) (w i))]
    abel
  rw [e]
  refine add_mem (sum_mem fun l _ => Submodule.smul_mem _ _ (hF _ _ hws)) (sum_mem fun i _ => sum_mem fun l _ =>
    Submodule.smul_mem _ _ (hw i (c l)))

end Lie

end GlobalTheory.HTGlueLie

namespace GlobalTheory.HTGlueLie

theorem sub_mem_of_inv {C M : Type*} [CommRing C] [AddCommGroup M] [Module C M] (E : Submodule C M) {a ρ ρb : C}
    (hk : a * (ρ - ρb) = 1) {e e' X : M} (he' : e' = a • (X - ρb • e)) (he : X - ρ • e ∈ E) : e - e' ∈ E := by
  subst he'
  have h : e - a • (X - ρb • e) = (-a) • (X - ρ • e) := by
    linear_combination (norm := module) -(hk • e)
  rw [h]
  exact E.smul_mem _ he

theorem sub_mem_trans {C M : Type*} [Ring C] [AddCommGroup M] [Module C M] (E : Submodule C M) {e e' s : M}
    (h1 : e - e' ∈ E) (h2 : e' - s ∈ E) : e - s ∈ E := by
  have := add_mem h1 h2
  rwa [sub_add_sub_cancel] at this

end GlobalTheory.HTGlueLie

namespace GlobalTheory.HTGlueLie

open GlobalTheory.HTCount in

theorem glueFil_lie : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - algebraMap k (TrivSqZeroExt k (Fin d → k)) (β b.ρ) • e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f) → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - algebraMap k (TrivSqZeroExt k (Fin d → k)) (β (b.t i c)) • w i ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) ∧ e - ∑ i, w i ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β hs φ _ d f hf e he
  have hT : ∀ (x : D.O) (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) (u : CrysC k d o₀.A),
      crd o₀.A π ((haveI := o₀.act.hom x; push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
        (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act x)) u) =
        crysAct o₀ x (crd o₀.A π u) := fun x π u => by
    haveI := o₀.act.hom x
    exact crd_push o₀.A π _ u
  have hZ := lieZ_le_fil o₀ β hs
  have hfZ : ∀ j, ∀ x ∈ lieZ o₀ β, f j x ∈ Fil o₀.A := fun j => (hf j).2.1
  have hδ := root_sub_ne_zero b β
  have hex : ∃ e' : CrysC k d o₀.A, e' = algebraMap k (TrivSqZeroExt k (Fin d → k))
      (β b.ρ - ((D.tr : k) - β b.ρ))⁻¹ •
      ((haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
        (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω))) e -
        algebraMap k (TrivSqZeroExt k (Fin d → k)) ((D.tr : k) - β b.ρ) • e) := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ := hex
  have hrho : ∀ π, crd o₀.A π e' ∈ rhoPart o₀ β := fun π => by
    rw [he', crd_smul, map_sub, hT, crd_smul]
    exact smul_mem_rhoPart o₀ β _ _
  choose r lam c hc using fun i => exists_combo (fun j => β.comp (b.t j)) (injective_chars b β)
    (fun j => if i = j then (1 : k) else 0)
  have hc' : ∀ i j, ∑ l, lam i l * β (b.t j (c i l)) = if i = j then 1 else 0 := hc
  refine ⟨fun i => ∑ l, algebraMap k (TrivSqZeroExt k (Fin d → k)) (lam i l) •
    (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O (c i l)); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
        (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O (c i l)))) e',
    fun i c₀ => ?_, ?_⟩
  · refine mem_glueFil_of_crd_mem o₀.A f _ hZ hfZ _ fun π => ?_
    have H := mul_sub_mem_lieZ o₀ β (lam i) (c i) i (hc' i) (hrho π) c₀
    convert H using 1
    simp only [map_sub, map_sum, hT, crd_smul]
  · have hk : algebraMap k (TrivSqZeroExt k (Fin d → k)) (β b.ρ - ((D.tr : k) - β b.ρ))⁻¹ *
        (algebraMap k (TrivSqZeroExt k (Fin d → k)) (β b.ρ) -
          algebraMap k (TrivSqZeroExt k (Fin d → k)) ((D.tr : k) - β b.ρ)) = 1 := by
      rw [← map_sub, ← map_mul, inv_mul_cancel₀ hδ, map_one]
    refine sub_mem_trans _ (sub_mem_of_inv _ hk he' he) ?_
    refine mem_glueFil_of_crd_mem o₀.A f _ hZ hfZ _ fun π => ?_
    have H := one_sub_mem_lieZ o₀ β lam c hc' (hrho π)
    convert H using 1
    simp only [map_sub, map_sum, hT, crd_smul]

end GlobalTheory.HTGlueLie
