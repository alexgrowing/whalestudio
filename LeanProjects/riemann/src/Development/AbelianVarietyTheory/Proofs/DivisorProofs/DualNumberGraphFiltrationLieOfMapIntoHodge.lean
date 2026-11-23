import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise.LieCond

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]

theorem push_coords (g : A₀ ⟶ A₀) [IsMonHom g] {d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀} {u v : HdR A₀}
    (h : ∀ c : primDR A₀, d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c))
    (c : primDR A₀) :
    push (epsDP k) (GlobalTheory.DeRham.epsRed k) g d ((constMor A₀).pull c) =
      TrivSqZeroExt.inl (push (dp0 k) (𝟙 _) g u c) + TrivSqZeroExt.inr (push (dp0 k) (𝟙 _) g v c) := by
  have k' := (homMor (dp0 k) (𝟙 _) g).comp (constMor A₀)
  have e1 : primPull (epsDP k) (GlobalTheory.DeRham.epsRed k) g ((constMor A₀).pull c) = k'.pull c :=
    GrpMor.pull_pull (constMor A₀) (homMor _ _ g) k' (fun _ => rfl) (by simp) c
  have e2 : (constMor A₀).pull (primPull (dp0 k) (𝟙 _) g c) = k'.pull c :=
    GrpMor.pull_pull (homMor _ _ g) (constMor A₀) k' (fun _ => rfl) rfl c
  rw [push_apply, e1, ← e2, h]
  rfl

theorem smul_coords (r : k) {d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀} {u v : HdR A₀}
    (h : ∀ c : primDR A₀, d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c))
    (c : primDR A₀) :
    (algebraMap k (DualNumber k) r • d) ((constMor A₀).pull c) =
      TrivSqZeroExt.inl ((r • u) c) + TrivSqZeroExt.inr ((r • v) c) := by
  rw [LinearMap.smul_apply, h, smul_eq_mul]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem mem_graphFil_iff_coords {f : HdR A₀ →ₗ[k] HdR A₀} {d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀}
    {u v : HdR A₀}
    (h : ∀ c : primDR A₀, d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c)) :
    d ∈ graphFil A₀ f ↔ u ∈ Fil A₀ ∧ v - f u ∈ Fil A₀ := by
  constructor
  · rintro ⟨x, hx, y, hy, e⟩
    have hu : u = x := LinearMap.ext fun c => by
      have := congrArg TrivSqZeroExt.fst ((h c).symm.trans (e c)); simpa using this
    have hv : v = f x + y := LinearMap.ext fun c => by
      have := congrArg TrivSqZeroExt.snd ((h c).symm.trans (e c)); simpa using this
    subst hu hv
    exact ⟨hx, by simpa using hy⟩
  · rintro ⟨hu, hv⟩
    exact ⟨u, hu, v - f u, hv, fun c => by rw [h c]; simp⟩

end GlobalTheory.HTRealise.LieCond

namespace GlobalTheory.HTRealise.LieCond

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {s : Sp k ⟶ Sp R}

def algAct (o₀ : GlobalTheory.UPel.HT.Obj b N s) : MonoidAlgebra k (𝓞 D.F) →ₐ[k] Module.End k (HdR o₀.A) :=
  MonoidAlgebra.lift k (Module.End k (HdR o₀.A)) (𝓞 D.F) ((GlobalTheory.HTCount.crysAct o₀).comp (algebraMap (𝓞 D.F) D.O)).toMonoidHom

def algChar (b : GlobalTheory.UPel.HT.Base D R) (β : R →+* k) (i : Fin D.a) : MonoidAlgebra k (𝓞 D.F) →ₐ[k] k :=
  MonoidAlgebra.lift k k (𝓞 D.F) (β.comp (b.t i)).toMonoidHom

theorem algAct_single (o₀ : GlobalTheory.UPel.HT.Obj b N s) (c : 𝓞 D.F) :
    algAct o₀ (MonoidAlgebra.single c (1 : k)) = GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O c) := by
  simp [algAct]

theorem algChar_single (β : R →+* k) (i : Fin D.a) (c : 𝓞 D.F) :
    algChar b β i (MonoidAlgebra.single c (1 : k)) = β (b.t i c) := by
  simp [algAct, algChar]

theorem algAct_mem_lieZ (o₀ : GlobalTheory.UPel.HT.Obj b N s) (β : R →+* k) (g : MonoidAlgebra k (𝓞 D.F))
    (hg : ∀ i, algChar b β i g = 0) {y : HdR o₀.A} (hy : y ∈ GlobalTheory.HTCount.rhoPart o₀ β) :
    algAct o₀ g y ∈ GlobalTheory.HTCount.lieZ o₀ β := by
  apply Submodule.subset_span
  refine ⟨g.coeff.support.card, fun l => g.coeff (g.coeff.support.equivFin.symm l),
    fun l => (g.coeff.support.equivFin.symm l : 𝓞 D.F),
    y, hy, fun i => ?_, ?_⟩
  · have := hg i
    rw [algChar, MonoidAlgebra.lift_apply, Finsupp.sum, ← Finset.sum_coe_sort g.coeff.support,
      ← Equiv.sum_comp g.coeff.support.equivFin.symm] at this
    simpa [smul_eq_mul] using this
  · rw [algAct, MonoidAlgebra.lift_apply, Finsupp.sum, ← Finset.sum_coe_sort g.coeff.support,
      ← Equiv.sum_comp g.coeff.support.equivFin.symm, LinearMap.sum_apply]
    rfl

theorem exists_idem (β : R →+* k) (hx : ∀ i j : Fin D.a, i ≠ j → ∃ x, β (b.t i x) ≠ β (b.t j x)) :
    ∃ e : Fin D.a → MonoidAlgebra k (𝓞 D.F), ∀ i j, algChar b β j (e i) = if j = i then 1 else 0 := by
  have : ∀ i j : Fin D.a, ∃ x, i ≠ j → β (b.t i x) ≠ β (b.t j x) := fun i j => by
    by_cases h : i = j
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨x, hx⟩ := hx i j h; exact ⟨x, fun _ => hx⟩
  choose x hx' using this
  let q : Fin D.a → Fin D.a → MonoidAlgebra k (𝓞 D.F) := fun i j =>
    (β (b.t i (x i j)) - β (b.t j (x i j)))⁻¹ •
      (MonoidAlgebra.single (x i j) 1 - algebraMap k _ (β (b.t j (x i j))))
  have hq : ∀ i j m, algChar b β m (q i j) =
      (β (b.t i (x i j)) - β (b.t j (x i j)))⁻¹ * (β (b.t m (x i j)) - β (b.t j (x i j))) := by
    intro i j m
    simp only [q, map_smul, map_sub, algChar_single, AlgHom.commutes, smul_eq_mul]
    rfl
  refine ⟨fun i => ∏ j ∈ Finset.univ.erase i, q i j, fun i m => ?_⟩
  rw [map_prod]
  split_ifs with h
  · rw [h]
    refine Finset.prod_eq_one fun j hj => ?_
    rw [hq]
    exact inv_mul_cancel₀ (sub_ne_zero.2 (hx' i j (Finset.ne_of_mem_erase hj).symm))
  · refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ m⟩) ?_
    rw [hq, sub_self, mul_zero]

theorem chars_ne (β : R →+* k) : ∀ i j : Fin D.a, i ≠ j → ∃ x, β (b.t i x) ≠ β (b.t j x) := by
  intro i j hij
  by_contra h
  simp only [not_exists, not_not] at h
  have h1 := congrArg (Ideal.map β) (b.comax i j hij)
  rw [Ideal.map_span, Ideal.map_top] at h1
  have h2 : Ideal.span (β '' Set.range fun x => b.t i x - b.t j x) = ⊥ := by
    rw [Ideal.span_eq_bot]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    simp [map_sub, h x]
  rw [h2] at h1
  exact bot_ne_top h1

theorem delta_ne (β : R →+* k) : β b.ρ - ((D.tr : k) - β b.ρ) ≠ 0 := by
  have hρ := congrArg β b.ρ_root
  simp only [map_add, map_sub, map_pow, map_mul, map_intCast, map_zero] at hρ
  set n : ℕ := (4 * D.nm - D.tr ^ 2).toNat
  have hpos : 0 < 4 * D.nm - D.tr ^ 2 := by linarith [D.disc_neg]
  have hn : (n : ℤ) = 4 * D.nm - D.tr ^ 2 := Int.toNat_of_nonneg hpos.le
  have hcop : n.Coprime p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 fun hd => D.disc_p ?_)
    have : (p : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.2 hd
    rw [hn] at this
    have h' : D.tr ^ 2 - 4 * D.nm = -(4 * D.nm - D.tr ^ 2) := by ring
    rw [h']; exact (dvd_neg).2 this
  have hu : IsUnit (n : k) := by
    have := (b.unit n hcop).map β
    simpa using this
  intro h0
  apply hu.ne_zero
  have hnk : (n : k) = ((4 * D.nm - D.tr ^ 2 : ℤ) : k) := by rw [← hn]; simp
  rw [hnk]
  push_cast
  have : (β b.ρ - ((D.tr : k) - β b.ρ)) ^ 2 = 0 := by rw [h0]; ring
  linear_combination -this + 4 * hρ

end GlobalTheory.HTRealise.LieCond

namespace GlobalTheory.HTRealise.LieCond

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {s : Sp k ⟶ Sp R}

theorem algAct_smul_apply (o₀ : GlobalTheory.UPel.HT.Obj b N s) (r : k) (g : MonoidAlgebra k (𝓞 D.F)) (z : HdR o₀.A) :
    algAct o₀ (r • g) z = r • algAct o₀ g z := by
  have := (algAct o₀).toLinearMap.map_smul r g
  exact LinearMap.congr_fun this z

theorem algAct_mul_apply (o₀ : GlobalTheory.UPel.HT.Obj b N s) (g h : MonoidAlgebra k (𝓞 D.F)) (z : HdR o₀.A) :
    algAct o₀ (g * h) z = algAct o₀ g (algAct o₀ h z) := by
  rw [map_mul]
  rfl

theorem algAct_single_apply (o₀ : GlobalTheory.UPel.HT.Obj b N s) (c : 𝓞 D.F) (z : HdR o₀.A) :
    haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c)
    algAct o₀ (MonoidAlgebra.single c (1 : k)) z = push (dp0 k) (𝟙 _) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) z := by
  rw [algAct_single]
  rfl

end GlobalTheory.HTRealise.LieCond

namespace GlobalTheory.HTRealise.LieCond

theorem inv_sub_smul_sub_sub_inv_sub_smul_sub_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (X z : V) (r r' : k)
    (h : r - r' ≠ 0) : (r - r')⁻¹ • (X - r' • z) - (r - r')⁻¹ • (X - r • z) = z := by
  rw [← smul_sub, show X - r' • z - (X - r • z) = (r - r') • z by rw [sub_smul]; abel, inv_smul_smul₀ h]

theorem smul_add_sub_linearMap_smul_add_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (f : V →ₗ[k] V) (a : k)
    (X Y P Q : V) : (a • Y + Q) - f (a • X + P) = a • (Y - f X) + (Q - f P) := by
  rw [map_add, map_smul, smul_sub]
  abel

theorem sub_eq_neg_smul_add_of_sub_smul_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (u u' S X : V) (a : k)
    (h : u' - a • X = u) : u - S = (-a) • X + (u' - S) := by
  rw [← h, neg_smul]
  abel

end GlobalTheory.HTRealise.LieCond

namespace GlobalTheory.HTRealise.LieCond

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]

theorem coords_sub {d d' : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀} {u v u' v' : HdR A₀}
    (h : ∀ c : primDR A₀, d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c))
    (h' : ∀ c : primDR A₀, d' ((constMor A₀).pull c) = TrivSqZeroExt.inl (u' c) + TrivSqZeroExt.inr (v' c))
    (c : primDR A₀) :
    (d - d') ((constMor A₀).pull c) = TrivSqZeroExt.inl ((u - u') c) + TrivSqZeroExt.inr ((v - v') c) := by
  rw [LinearMap.sub_apply, h, h']
  ext <;> simp

theorem coords_sum {Idx : Type} (s : Finset Idx) (d : Idx → Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀)
    (u v : Idx → HdR A₀)
    (h : ∀ i, ∀ c : primDR A₀, d i ((constMor A₀).pull c) = TrivSqZeroExt.inl (u i c) + TrivSqZeroExt.inr (v i c))
    (c : primDR A₀) :
    (∑ i ∈ s, d i) ((constMor A₀).pull c) =
      TrivSqZeroExt.inl ((∑ i ∈ s, u i) c) + TrivSqZeroExt.inr ((∑ i ∈ s, v i) c) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, Finset.sum_empty, LinearMap.zero_apply]
    ext <;> simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, h, ih]
    ext <;> simp

end GlobalTheory.HTRealise.LieCond

namespace GlobalTheory.HTRealise

set_option maxHeartbeats 2000000 in
open LieCond in

theorem eigen_decomp_graphFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R)
    (o₀ : GlobalTheory.UPel.HT.Obj b N s) (f : HdR o₀.A →ₗ[k] HdR o₀.A), GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A →
    (∀ x ∈ GlobalTheory.HTCount.lieZ o₀ β, f x ∈ Fil o₀.A) → ∀ d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) o₀.A,
    (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
      push (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d) -
      algebraMap k (DualNumber k) (β b.ρ) • d ∈ GlobalTheory.HTRealise.graphFil o₀.A f →
    ∃ w : Fin D.a → Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) o₀.A,
      (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c);
        push (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) -
        algebraMap k (DualNumber k) (β (b.t i c)) • w i ∈ GlobalTheory.HTRealise.graphFil o₀.A f) ∧
      d - ∑ i, w i ∈ GlobalTheory.HTRealise.graphFil o₀.A f := by
  intro p _ D R _ b N k _ β s o₀ f hZ hfZ d hd
  haveI := o₀.act.hom
  obtain ⟨u, v, huv⟩ := exists_coords d
  set Ω := GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) with hΩ
  set ρ := β b.ρ with hρ
  set ρ' := (D.tr : k) - ρ with hρ'
  set δ := ρ - ρ' with hδdef
  have hδ : δ ≠ 0 := delta_ne (b := b) β
  have hcoord := coords_sub (fun c => push_coords (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) huv c)
    (fun c => smul_coords ρ huv c)
  obtain ⟨hx, hy⟩ := (mem_graphFil_iff_coords (f := f) hcoord).1 hd
  change Ω u - ρ • u ∈ Fil o₀.A at hx
  change Ω v - ρ • v - f (Ω u - ρ • u) ∈ Fil o₀.A at hy
  obtain ⟨e, he⟩ := exists_idem (b := b) β (chars_ne β)
  obtain ⟨u', hu'def⟩ : ∃ u', u' = δ⁻¹ • (Ω u - ρ' • u) := ⟨_, rfl⟩
  obtain ⟨v', hv'def⟩ : ∃ v', v' = δ⁻¹ • (Ω v - ρ' • v) := ⟨_, rfl⟩
  have hrho : ∀ z, δ⁻¹ • (Ω z - ρ' • z) ∈ GlobalTheory.HTCount.rhoPart o₀ β := fun z =>
    Submodule.smul_mem _ _ ⟨z, by simp [Ω, ρ', ρ]⟩
  have key : ∀ g, (∀ j, algChar b β j g = 0) →
      algAct o₀ g u' ∈ Fil o₀.A ∧ algAct o₀ g v' - f (algAct o₀ g u') ∈ Fil o₀.A := fun g hg =>
    ⟨hZ (algAct_mem_lieZ o₀ β g hg (hu'def ▸ hrho u)),
      sub_mem (hZ (algAct_mem_lieZ o₀ β g hg (hv'def ▸ hrho v)))
        (hfZ _ (algAct_mem_lieZ o₀ β g hg (hu'def ▸ hrho u)))⟩
  choose w hw using fun i => exists_crys o₀.ab (algAct o₀ (e i) u') (algAct o₀ (e i) v')
  refine ⟨w, ?_, ?_⟩
  · intro i c
    have hc := coords_sub (fun c' => push_coords (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (hw i) c')
      (fun c' => smul_coords (β (b.t i c)) (hw i) c')
    rw [mem_graphFil_iff_coords hc]
    have hg : ∀ j, algChar b β j (MonoidAlgebra.single c (1 : k) * e i - β (b.t i c) • e i) = 0 := by
      intro j
      rw [map_sub, map_mul, map_smul, algChar_single, he, smul_eq_mul]
      split_ifs with h
      · rw [h]; ring
      · ring
    have e1 : ∀ z, push (dp0 k) (𝟙 _) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (algAct o₀ (e i) z) -
        β (b.t i c) • algAct o₀ (e i) z = algAct o₀ (MonoidAlgebra.single c (1 : k) * e i - β (b.t i c) • e i) z := by
      intro z
      rw [map_sub, LinearMap.sub_apply, algAct_mul_apply, algAct_smul_apply, algAct_single_apply]
    rw [e1, e1]
    exact key _ hg
  · have hs := coords_sub huv (coords_sum Finset.univ w (fun i => algAct o₀ (e i) u') (fun i => algAct o₀ (e i) v')
      (fun i c => hw i c))
    rw [mem_graphFil_iff_coords hs]
    have hg0 : ∀ j, algChar b β j (1 - ∑ i, e i) = 0 := by
      intro j
      rw [map_sub, map_one, map_sum]
      simp [he]
    obtain ⟨k1, k2⟩ := key _ hg0
    have decu : u' - δ⁻¹ • (Ω u - ρ • u) = u := by rw [hu'def]; exact inv_sub_smul_sub_sub_inv_sub_smul_sub_eq _ _ _ _ hδ
    have decv : v' - δ⁻¹ • (Ω v - ρ • v) = v := by rw [hv'def]; exact inv_sub_smul_sub_sub_inv_sub_smul_sub_eq _ _ _ _ hδ
    have hsum : ∀ z, algAct o₀ (1 - ∑ i, e i) z = z - ∑ i, algAct o₀ (e i) z := by
      intro z
      rw [map_sub, map_one, map_sum, LinearMap.sub_apply, LinearMap.sum_apply]
      rfl
    rw [sub_eq_neg_smul_add_of_sub_smul_eq u u' _ _ _ decu, sub_eq_neg_smul_add_of_sub_smul_eq v v' _ _ _ decv, ← hsum, ← hsum]
    refine ⟨add_mem (Submodule.smul_mem _ _ hx) k1, ?_⟩
    rw [smul_add_sub_linearMap_smul_add_eq]
    exact add_mem (Submodule.smul_mem _ _ hy) k2

end GlobalTheory.HTRealise
