import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSectionCompatibleSquareThickeningStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineCoverSquarePolarisationSectionsStatement

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgebraiseGen

open GlobalTheory.Algebraise GlobalTheory.SectionRingIso ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

variable {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsAdicComplete I R]

theorem existsUnique_rel_of_lim (P : PolAV (Spec (CommRingCat.of R))) {M : LB P.A.left} (hM : M.IsLB)
    (hlim : ∀ n : ℕ, 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => (fstG I e P.A).left)
      (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z)
        (J : (Z ⟶ P.A.left) → M.ι), Good M z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) →
      ∃! σ : H0 M n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z)
        (J : (Z ⟶ P.A.left) → M.ι), Good M z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J)
    {X : Scheme.{0}} {L : LB X}
    (hL : L.IsLB) (g : ∀ e, (thickObj R I e P.A).left ⟶ X)
    (v : ∀ e, LB.Iso (M.pull (fstG I e P.A).left) (L.pull (g e))) (hv : ∀ e, (v e).IsGen)
    (hg : ∀ e, thickMap R I e P.A ≫ g (e + 1) = g e)
    (hc : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (j : L.ι) (j' : M.ι),
      g e (r z) ∈ L.U j → (fstG I e P.A).left (r z) ∈ M.U j' →
      gw (v (e + 1)) (r ≫ thickMap R I e P.A) z j (fun _ => j') = gw (v e) r z j (fun _ => j'))
    {n : ℕ} (hn : 1 ≤ n) (b : H0 L n) :
    ∃! a : H0 M n, Rel (T := fun e => (thickObj R I e P.A).left) g (fun e => (fstG I e P.A).left) v a b := by
  choose s hs using fun e => exists_down hL hM (g e) (fstG I e P.A).left (v e) (hv e) b
  have cancel : ∀ {T : Type} [CommRing T] (u : Tˣ) {x y : T}, u.val ^ n * x = u.val ^ n * y → x = y :=
    fun u _ _ h => (u.isUnit.pow n).mul_left_cancel h
  have sv : ∀ (a : H0 M n) (Z : Scheme.{0}) (q : Z ⟶ P.A.left) (z : Z) (J),
      sval a q z J = vl a q z (fun _ => J q) := fun a Z q z J =>
    sval_of a q z J (fun _ => J q) fun _ => by rw [Category.comp_id]
  obtain ⟨a, ha, hu⟩ := hlim n hn s fun e Z r z J hJ => by
    obtain ⟨j, hj⟩ := exists_chart hL (g e (r z))
    have hj' : (fstG I e P.A).left (r z) ∈ M.U (J (r ≫ (fstG I e P.A).left)) := hJ _
    have e₁ : (r ≫ thickMap R I e P.A) ≫ g (e + 1) = r ≫ g e := by rw [Category.assoc, hg]
    have e₂ : (r ≫ thickMap R I e P.A) ≫ (fstG I (e + 1) P.A).left = r ≫ (fstG I e P.A).left := by
      rw [Category.assoc, thickMap_fstG]
    have h₁ := hs (e + 1) Z (r ≫ thickMap R I e P.A) z j (J (r ≫ (fstG I e P.A).left))
      ((congrArg (fun q : Z ⟶ X => q z ∈ L.U j) e₁).mpr hj)
      ((congrArg (fun q : Z ⟶ P.A.left => q z ∈ M.U _) e₂).mpr hj')
    rw [e₁, hc e Z r z j _ hj hj', hs e Z r z j _ hj hj'] at h₁
    exact (sval_of (s (e + 1)) _ z J (fun _ => J (r ≫ (fstG I e P.A).left)) fun _ => congrArg J e₂).trans
      (cancel _ h₁).symm
  refine ⟨a, fun e Z r z j j' hj hj' => ?_, fun a' ha' => hu a' fun e Z r z J hJ => ?_⟩
  · obtain ⟨J, hJ, eJ⟩ := exists_good M hM z (K := Fin 1) (fun _ => r ≫ (fstG I e P.A).left) (fun _ => j')
      (fun _ _ _ => rfl) (fun _ => hj')
    have := ha e Z r z J hJ
    rw [sv, eJ 0, sval_of (s e) r z J (fun _ => j') fun _ => eJ 0] at this
    rw [this]
    exact hs e Z r z j j' hj hj'
  · obtain ⟨j, hj⟩ := exists_chart hL (g e (r z))
    have hj' : (fstG I e P.A).left (r z) ∈ M.U (J (r ≫ (fstG I e P.A).left)) := hJ _
    rw [sv]
    exact cancel _ ((ha' e Z r z j _ hj hj').symm.trans (hs e Z r z j _ hj hj'))

end GlobalTheory.AlgebraiseGen

namespace GlobalTheory.AlgebraiseGen

open GlobalTheory.Algebraise GlobalTheory.SectionRingIso ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem exists_iso_of_compatible_thickenings_gen {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (M : LB P.A.left) (M' : LB P'.A.left)
    (hM : M.IsLB) (hM' : M'.IsLB)
    (hlim : ∀ n : ℕ, 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => (fstG I e P.A).left)
      (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z)
        (J : (Z ⟶ P.A.left) → M.ι), Good M z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) →
      ∃! σ : H0 M n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z)
        (J : (Z ⟶ P.A.left) → M.ι), Good M z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J)
    (hlim' : ∀ n : ℕ, 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => (fstG I e P'.A).left)
      (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z)
        (J : (Z ⟶ P'.A.left) → M'.ι), Good M' z J → sval (s (e + 1)) (r ≫ thickMap R I e P'.A) z J = sval (s e) r z J) →
      ∃! σ : H0 M' n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z)
        (J : (Z ⟶ P'.A.left) → M'.ι), Good M' z J → sval σ (r ≫ (fstG I e P'.A).left) z J = sval (s e) r z J)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀)
    (hcov : ∀ n : ℕ, n₀ ≤ n → ∃ (κ : Type) (s : κ → H0 M n), (⨆ i, nonzeroLocus (s i) = ⊤) ∧
      ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (hcov' : ∀ n : ℕ, n₀ ≤ n → ∃ (κ : Type) (s : κ → H0 M' n), (⨆ i, nonzeroLocus (s i) = ⊤) ∧
      ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A)
    (v : ∀ e : ℕ, LB.Iso (M'.pull (fstG I e P'.A).left) (M.pull ((β e).hom.left ≫ (fstG I e P.A).left)))
    (hv : ∀ e, (v e).IsGen)
    (hβ : ∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A)
    (hc : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : M.ι) (j' : M'.ι),
      (fstG I e P.A).left ((β e).hom.left (r z)) ∈ M.U j → (fstG I e P'.A).left (r z) ∈ M'.U j' →
      gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z j (fun _ => j') = gw (v e) r z j (fun _ => j')) :
    ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso M' (M.pull Φ.hom.left)), w.IsGen ∧
    ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : M.ι) (j' : M'.ι),
        (fstG I e P.A).left ((β e).hom.left (r z)) ∈ M.U j → (fstG I e P'.A).left (r z) ∈ M'.U j' →
        gw w (r ≫ (fstG I e P'.A).left) z j j' = gw (v e) r z j (fun _ => j') := by
  have prop : ∀ Q : PolAV (Spec (CommRingCat.of R)), IsProper Q.A.hom := fun Q => Q.isAb.proper
  have cpt : ∀ Q : PolAV (Spec (CommRingCat.of R)), CompactSpace Q.A.left := fun Q =>
    have := prop Q; QuasiCompact.compactSpace_of_compactSpace Q.A.hom
  have qs : ∀ Q : PolAV (Spec (CommRingCat.of R)), QuasiSeparatedSpace Q.A.left := fun Q =>
    have := prop Q; quasiSeparatedSpace_of_quasiSeparated Q.A.hom
  have := prop P; have := prop P'; have := cpt P; have := cpt P'; have := qs P; have := qs P'
  have hi : ∀ e, (β e).hom.left ≫ (β e).inv.left = 𝟙 _ := fun e => by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  have ih : ∀ e, (β e).inv.left ≫ (β e).hom.left = 𝟙 _ := fun e => by rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have hβ' : ∀ e, thickMap R I e P.A ≫ (β (e + 1)).inv.left = (β e).inv.left ≫ thickMap R I e P'.A := fun e => by
    have : (β e).inv.left ≫ (thickMap R I e P'.A ≫ (β (e + 1)).hom.left) ≫ (β (e + 1)).inv.left =
        (β e).inv.left ≫ ((β e).hom.left ≫ thickMap R I e P.A) ≫ (β (e + 1)).inv.left := by rw [hβ]
    rw [Category.assoc, hi, Category.comp_id, Category.assoc, ← Category.assoc (β e).inv.left, ih,
      Category.id_comp] at this
    exact this.symm
  have eA : ∀ e, (β e).inv.left ≫ (β e).hom.left ≫ (fstG I e P.A).left = (fstG I e P.A).left := fun e => by
    rw [← Category.assoc, ih, Category.id_comp]
  have eB : ∀ e, (β e).hom.left ≫ (β e).inv.left ≫ (fstG I e P'.A).left = (fstG I e P'.A).left := fun e => by
    rw [← Category.assoc, hi, Category.id_comp]
  choose u hu hu' using fun e => exists_swap _ _ (v e) (hv e) (β e).inv.left (fstG I e P.A).left
    ((β e).inv.left ≫ (fstG I e P'.A).left) (eA e) rfl
  let Rl : ∀ n : ℕ, H0 M' n → H0 M n → Prop := fun n a b =>
    Rel (T := fun e => (thickObj R I e P'.A).left) (fun e => (β e).hom.left ≫ (fstG I e P.A).left)
      (fun e => (fstG I e P'.A).left) v a b
  have E₁ : ∀ n, 1 ≤ n → ∀ b, ∃! a, Rl n a b := fun n hn b =>
    existsUnique_rel_of_lim I P' hM' hlim' hM _ v hv
      (fun e => by rw [← Category.assoc, hβ, Category.assoc, thickMap_fstG]) hc hn b
  have E₂ : ∀ n, 1 ≤ n → ∀ a, ∃! b, Rl n a b := fun n hn a => by
    have H := existsUnique_rel_of_lim I P hM hlim hM' (fun e => (β e).inv.left ≫ (fstG I e P'.A).left) u hu
      (fun e => by rw [← Category.assoc, hβ', Category.assoc, thickMap_fstG]) (fun e Z r z j' j hj' hj => by
        have e₁ : (r ≫ thickMap R I e P.A) ≫ (fstG I (e + 1) P.A).left = r ≫ (fstG I e P.A).left := by
          rw [Category.assoc, thickMap_fstG]
        have e₂ : (r ≫ thickMap R I e P.A) ≫ (β (e + 1)).inv.left ≫ (fstG I (e + 1) P'.A).left =
            r ≫ (β e).inv.left ≫ (fstG I e P'.A).left := by
          rw [Category.assoc, ← Category.assoc (thickMap R I e P.A), hβ', Category.assoc, thickMap_fstG]
        rw [hu' (e + 1) Z _ z j j' ((congrArg (fun q : Z ⟶ P.A.left => q z ∈ M.U j) e₁).mpr hj)
          ((congrArg (fun q : Z ⟶ P'.A.left => q z ∈ M'.U j') e₂).mpr hj'), hu' e Z r z j j' hj hj',
          Category.assoc, hβ', ← Category.assoc]
        exact congrArg (·⁻¹) (hc e Z (r ≫ (β e).inv.left) z j j'
          ((congrArg (fun q : Z ⟶ P.A.left => q z ∈ M.U j) (congrArg (r ≫ ·) (eA e))).mpr hj) hj')) hn a
    refine (existsUnique_congr fun b => ⟨fun h e Z r z j j' hj hj' => ?_, fun h e Z r z j' j hj' hj => ?_⟩).1 H
    · have m' := (congrArg (fun q : Z ⟶ P'.A.left => q z ∈ M'.U j') (congrArg (r ≫ ·) (eB e))).mpr hj'
      have := h e Z (r ≫ (β e).hom.left) z j' j m' hj
      rw [hu' e Z (r ≫ (β e).hom.left) z j j' hj m'] at this
      simp only [Category.assoc] at this
      rw [eB, hi, Category.comp_id] at this
      beta_reduce
      rw [this, ← _root_.mul_assoc, ← mul_pow, Units.mul_inv, one_pow, _root_.one_mul]
    · have m := (congrArg (fun q : Z ⟶ P.A.left => q z ∈ M.U j) (congrArg (r ≫ ·) (eA e))).mpr hj
      have := h e Z (r ≫ (β e).inv.left) z j j' m hj'
      simp only [Category.assoc] at this
      rw [eA] at this
      beta_reduce
      rw [hu' e Z r z j j' hj hj', this, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul]
  obtain ⟨θ, hθ⟩ : ∃ θ : ∀ n : ℕ, 1 ≤ n → (H0 M' n ≃ H0 M n), ∀ n hn a, Rl n a (θ n hn a) := by
    refine ⟨fun n hn => ⟨fun a => (E₂ n hn a).exists.choose, fun b => (E₁ n hn b).exists.choose, fun a => ?_,
      fun b => ?_⟩, fun n hn a => (E₂ n hn a).exists.choose_spec⟩
    · exact (E₁ n hn _).unique (E₁ n hn _).exists.choose_spec (E₂ n hn a).exists.choose_spec
    · exact (E₂ n hn _).unique (E₂ n hn _).exists.choose_spec (E₁ n hn b).exists.choose_spec
  have hbase : ∀ e, ((β e).hom.left ≫ (fstG I e P.A).left) ≫ P.A.hom = (fstG I e P'.A).left ≫ P'.A.hom := fun e => by
    rw [Category.assoc, fstG_hom, fstG_hom, ← Category.assoc, Over.w]
  have hlin : ∀ (n : ℕ) (hn : 1 ≤ n) (c : R) (a b d : H0 M' n),
      (∀ j, d.f j = a.f j + resTop _ (scal P'.A.hom c) * b.f j) →
      ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal P.A.hom c) * (θ n hn b).f j := by
    intro n hn c a b d h
    have : Rl n d (DVR.SecOps.secAdd (θ n hn a) (DVR.SecOps.secScale (scal P.A.hom c) (θ n hn b))) := by
      intro e Z r z j j' hj hj'
      rw [vl_add_scale (a := θ n hn a) (b := θ n hn b) (c := scal P.A.hom c) (fun _ => rfl) _ z hj,
        vl_add_scale h _ z hj', hθ n hn a e Z r z j j' hj hj', hθ n hn b e Z r z j j' hj hj', gs_scal, gs_scal,
        Category.assoc r, Category.assoc r, hbase]
      ring
    rw [(E₂ n hn d).unique (hθ n hn d) this]
    exact fun _ => rfl
  have hmul : ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 M' n) (b : H0 M' m) (d : H0 M' (n + m)),
      (∀ j : Fin 1 → M'.ι, (show Γ(P'.A.left, ch M' j) from d.f j) =
        (show Γ(P'.A.left, ch M' j) from a.f j) * (show Γ(P'.A.left, ch M' j) from b.f j)) →
      ∀ j : Fin 1 → M.ι, (show Γ(P.A.left, ch M j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) =
        (show Γ(P.A.left, ch M j) from (θ n hn a).f j) * (show Γ(P.A.left, ch M j) from (θ m hm b).f j) := by
    intro n m hn hm a b d h
    obtain ⟨d', hd'⟩ := exists_mul (θ n hn a) (θ m hm b)
    have : Rl (n + m) d d' := by
      intro e Z r z j j' hj hj'
      rw [vl_mul hd' _ z hj, vl_mul h _ z hj', hθ n hn a e Z r z j j' hj hj', hθ m hm b e Z r z j j' hj hj']
      ring
    rw [(E₂ _ (hn.trans (Nat.le_add_right n m)) d).unique (hθ _ _ d) this]
    exact hd'
  have h4 : 1 ≤ n₀ := hn₀
  obtain ⟨κ, t, ht, hta⟩ := hcov n₀ le_rfl
  obtain ⟨κ', s, hs, hsa⟩ := hcov' n₀ le_rfl
  obtain ⟨κ'', s₅, hs₅, -⟩ := hcov' (n₀ + 1) (Nat.le_succ n₀)
  have mt : ∀ x, ∃ i, x ∈ nonzeroLocus (t i) := fun x => Opens.mem_iSup.1 (by rw [ht]; trivial)
  have ms : ∀ x, ∃ i, x ∈ nonzeroLocus (s i) := fun x => Opens.mem_iSup.1 (by rw [hs]; trivial)
  have ms₅ : ∀ x, ∃ i, x ∈ nonzeroLocus (s₅ i) := fun x => Opens.mem_iSup.1 (by rw [hs₅]; trivial)
  choose d hd using fun p : κ' × κ => exists_mul (s p.1) ((θ n₀ h4).symm (t p.2))
  have l' := fun p => locus_mul hM' (hd p)
  have l : ∀ p, nonzeroLocus (θ (n₀ + n₀) (h4.trans (Nat.le_add_right n₀ n₀)) (d p)) =
      nonzeroLocus (θ n₀ h4 (s p.1)) ⊓ nonzeroLocus (t p.2) := fun p => by
    rw [locus_mul hM (hmul n₀ n₀ h4 h4 _ _ _ (hd p)), Equiv.apply_symm_apply]
  have mem : ∀ z, ∃ p, (fstG I 0 P'.A).left z ∈ nonzeroLocus (d p) := fun z => by
    obtain ⟨i, hi⟩ := ms ((fstG I 0 P'.A).left z)
    obtain ⟨k, hk⟩ := mt (((β 0).hom.left ≫ (fstG I 0 P.A).left) z)
    refine ⟨(i, k), (l' _).ge ⟨hi, (Rel.mem_iff hM hM' (hθ n₀ h4 _) 0 z).1 ?_⟩⟩
    rw [Equiv.apply_symm_apply]
    exact hk
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_iso_of_sectionRing_equiv_alt R P.A P'.A M M' hM hM' θ hlin hmul
    ⟨n₀ + n₀, h4.trans (Nat.le_add_right n₀ n₀), κ' × κ, d,
      eq_top_of_thick I P'.A _ fun z => Opens.mem_iSup.2 (mem z),
      eq_top_of_thick I P.A _ fun z => by
        obtain ⟨p, hp⟩ := mem ((β 0).inv.left z)
        have := (Rel.mem_iff hM hM' (hθ _ (h4.trans (Nat.le_add_right n₀ n₀)) (d p)) 0 _).2 hp
        exact Opens.mem_iSup.2 ⟨p, (congrArg (fun q : (thickObj R I 0 P.A).left ⟶ P.A.left => q z ∈ _) (eA 0)).mp this⟩,
      fun p => ⟨by
        rw [l', inf_comm]; exact isAffineOpen_nonzeroLocus_inf (LB.isLB_linComb hM' _ _) _ (hsa _), by
        rw [l]; exact isAffineOpen_nonzeroLocus_inf (LB.isLB_linComb hM _ _) _ (hta _)⟩⟩
  obtain ⟨w, hw, H⟩ := GlobalTheory.exists_iso_of_sectionRing R P.A P'.A M M' hM hM' θ hlin hmul Ψ.hom.left hΨ
    fun x => by
      obtain ⟨i, hi⟩ := ms x
      obtain ⟨k, hk⟩ := ms₅ x
      exact ⟨n₀, h4, s i, s₅ k, hi, hk⟩
  have H' : ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 M' n) (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (j : M.ι)
      (j' : M'.ι), Ψ.hom.left (r z) ∈ M.U j → r z ∈ M'.U j' →
      vl (θ n hn a) (r ≫ Ψ.hom.left) z (fun _ => j) = (gw w r z j j').val ^ n * vl a r z (fun _ => j') := by
    intro n hn a Z r z j j' hj hj'
    refine (H n hn a Z r z (fun _ => j) (fun _ => j') (fun _ => hj) (fun _ => hj')).trans ?_
    rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast, Units.val_pow_eq_pow_val]
  refine ⟨Ψ, w, hw, fun e => ?_⟩
  have key : (β e).hom.left ≫ (fstG I e P.A).left = (fstG I e P'.A).left ≫ Ψ.hom.left := by
    obtain ⟨y, hy, hy'⟩ := exists_swap _ _ (v e) (hv e) (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _)
    obtain ⟨y', T⟩ := exists_comp hM' w y ((isGen_iff w).1 hw) ((isGen_iff y).1 hy) hM
      (LB.isLB_pull hM _)
    refine hom_ext_of_sec_pull_eq _ _ M hM ⟨n₀, h4, κ, t, ht, hta⟩ _ _ y'
      ((isGen_iff y').2 (T.pgen_comp hM' ((isGen_iff w).1 hw) ((isGen_iff y).1 hy))) fun n hn b z j j' hj hj' => ?_
    obtain ⟨a, rfl⟩ := (θ n hn).surjective b
    obtain ⟨k, hk⟩ := exists_chart hM' ((fstG I e P'.A).left z)
    have h₁ := H' n hn a _ (fstG I e P'.A).left z j k hj hk
    have h₂ := hθ n hn a e _ (𝟙 ((Over.map (thick R I e)).obj (thickObj R I e P'.A)).left) z j' k hj' hk
    have h₃ := T _ (𝟙 _) z j k (fun _ => j') hj hk (mem_pull.2 hj')
    rw [hy' _ (𝟙 _) z j' k hj' hk] at h₃
    simp only [Category.id_comp] at h₂ h₃
    refine h₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (fun t => (t ^ n).val) h₃) h₂).symm)
    rw [Units.val_pow_eq_pow_val, ← _root_.mul_assoc, ← mul_pow, ← Units.val_mul, inv_mul_cancel_right]
  refine ⟨key.symm, fun Z r z j j' hj hj' => ?_⟩
  have hj₂ := (congrArg (fun q : (thickObj R I e P'.A).left ⟶ P.A.left => q (r z) ∈ M.U j) key).mp hj
  have pw : ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 M' n), (fstG I e P'.A).left (r z) ∈ nonzeroLocus a →
      gw w (r ≫ (fstG I e P'.A).left) z j j' ^ n = gw (v e) r z j (fun _ => j') ^ n := fun n hn a ha => by
    have h₁ := H' n hn a _ (r ≫ (fstG I e P'.A).left) z j j' hj₂ hj'
    have h₂ := hθ n hn a e _ r z j j' hj hj'
    rw [Category.assoc, ← key] at h₁
    exact Units.ext (((mem_iff_isUnit a (r ≫ (fstG I e P'.A).left) z (j := fun _ => j') hj').1 ha).mul_right_cancel
      (h₁.symm.trans h₂))
  obtain ⟨i, hi⟩ := ms ((fstG I e P'.A).left (r z))
  obtain ⟨k, hk⟩ := ms₅ ((fstG I e P'.A).left (r z))
  have a₅ := pw (n₀ + 1) (Nat.le_add_left 1 n₀) _ hk
  rw [pow_succ, pow_succ _ n₀, pw n₀ h4 _ hi] at a₅
  exact mul_left_cancel a₅

end GlobalTheory.AlgebraiseGen

open GlobalTheory.Algebraise GlobalTheory.SectionRingIso ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace in

theorem GlobalTheory.exists_iso_of_compatible_thickenings_sq : SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A)
    (v : ∀ e : ℕ, LB.Iso ((LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2)).pull (fstG I e P'.A).left)
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull ((β e).hom.left ≫ (fstG I e P.A).left))),
    (∀ e, (v e).IsGen) →
    (∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A) →
    (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
      (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
      gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z (fun _ => j) (fun _ => fun _ => j') =
        gw (v e) r z (fun _ => j) (fun _ => fun _ => j')) →
    ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso (LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2))
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen ∧
    ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
        (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
        gw w (r ≫ (fstG I e P'.A).left) z (fun _ => j) (fun _ => j') = gw (v e) r z (fun _ => j) (fun _ => fun _ => j') := by
  intro hS hA R _ _ _ I _ P P' β v hv hβ hc
  obtain ⟨Φ, w, hw, H⟩ := GlobalTheory.AlgebraiseGen.exists_iso_of_compatible_thickenings_gen I P P' _ _
    (LB.isLB_linComb P.isLB _ _) (LB.isLB_linComb P'.isLB _ _) (GlobalTheory.T.existsUnique_section_compatible_square_thickening hS R I P) (GlobalTheory.T.existsUnique_section_compatible_square_thickening hS R I P') 2 (by norm_num)
    (GlobalTheory.T.exists_affine_cover_square_polarisation_sections hA R P) (GlobalTheory.T.exists_affine_cover_square_polarisation_sections hA R P') β v hv hβ (fun e Z r z j j' hj hj' => by
      obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, fin_one_const j⟩
      obtain ⟨a', rfl⟩ : ∃ a', j' = fun _ => a' := ⟨j' 0, fin_one_const j'⟩
      exact hc e Z r z a a' (mem_ch.1 hj) (mem_ch.1 hj'))
  exact ⟨Φ, w, hw, fun e => ⟨(H e).1, fun Z r z j j' hj hj' =>
    (H e).2 Z r z (fun _ => j) (fun _ => j') (mem_ch.2 hj) (mem_ch.2 hj')⟩⟩
