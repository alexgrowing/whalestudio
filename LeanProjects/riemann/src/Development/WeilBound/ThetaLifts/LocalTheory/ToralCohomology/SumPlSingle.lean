import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ShiftLow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

open FockH1Action PositivityTheory.KReal Polynomial
open scoped TensorProduct

namespace PositivityTheory.ThKG.CayleyTransformDarboux

variable {r s : ℕ}

theorem poly_step {M : Type} [AddCommGroup M] [Module ℂ M] (C : Module.End ℂ M) (c : ℂ) (V : Submodule ℂ M)
    (hinj : ∀ x, C x - c • x ∈ V → x ∈ V) (x : M) :
    ∀ n (p : ℂ[X]), p.natDegree = n → p ≠ 0 → aeval C p x ∈ V → ∃ p' : ℂ[X], p'.eval c ≠ 0 ∧ aeval C p' x ∈ V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hn h0 hp
    by_cases e : p.eval c = 0
    · obtain ⟨p', rfl⟩ := dvd_iff_isRoot.2 e
      have h' : p' ≠ 0 := right_ne_zero_of_mul h0
      refine ih p'.natDegree ?_ p' rfl h' (hinj _ ?_)
      · rw [← hn, natDegree_mul (X_sub_C_ne_zero c) h', natDegree_X_sub_C]; omega
      · simpa [Algebra.algebraMap_eq_smul_one] using hp
    · exact ⟨p, e, hp⟩

theorem aeval_int {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {C : Module.End ℂ M}
    {C' : Module.End ℂ M'} (φ : M →ₗ[ℂ] M') (h : ∀ x, φ (C x) = C' (φ x)) (p : ℂ[X]) (x : M) :
    φ (aeval C p x) = aeval C' p (φ x) := by
  induction p using Polynomial.induction_on generalizing x with
  | C a => simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval C'), aeval_X, aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem aeval_mem {M : Type} [AddCommGroup M] [Module ℂ M] {C : Module.End ℂ M} {V : Submodule ℂ M} (h : ∀ x ∈ V, C x ∈ V)
    (p : ℂ[X]) {x : M} (hx : x ∈ V) : aeval C p x ∈ V := by
  have := aeval_int (C := C.restrict h) (C' := C) V.subtype (fun _ => rfl) p ⟨x, hx⟩
  rw [show aeval C p x = _ from this.symm]
  exact Subtype.mem _

def hD : Ix r s → ℝ
  | .inl i => -(i : ℝ)
  | .inr i => -(i : ℝ)

theorem hD_pos {a b : Ix r s} (h : posC a b) : hD b < hD a := by
  rcases a with i | i <;> rcases b with j | j <;> simp only [posC] at h <;> simp only [hD] <;>
    exact neg_lt_neg (by exact_mod_cast h)

def one {M : Type} [AddCommGroup M] [Module ℂ M] (act : Mat r s →ₗ[ℂ] Module.End ℂ M) :
    (Unit → Mat r s) →ₗ[ℂ] Module.End ℂ M := act ∘ₗ LinearMap.proj ()

theorem side_one {La : Ix r s → ℚ} {T : Type} [AddCommGroup T] [Module ℂ T] {act : Mat r s →ₗ[ℂ] Module.End ℂ T}
    (h : Side La T act) : ∃ f : T, HwK (units act) La f ∧ genG act (Submodule.span ℂ {f}) = ⊤ ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (act' : Mat r s →ₗ[ℂ] Module.End ℂ M), IsLie act' →
        ∀ (J : Type) [Fintype J] (φ : J → T →ₗ[ℂ] M) (x : J → T), (∀ i Y y, φ i (act Y y) = act' Y (φ i y)) →
          HwK (units act') La (∑ i, φ i (x i)) → ∃ c : J → ℂ, ∑ i, φ i (x i) = ∑ i, c i • φ i f := by
  classical
  obtain ⟨hL, hT, A, _, _, _, ρ, ι, f, hadj, hgl, hw, hι, hgen, hs⟩ := h
  have hwf : HwK (units act) La (ι f) :=
    ⟨fun a => by rw [units, ← hι a a (sb_refl a), hw.1, map_smul],
      fun a b e => by rw [units, ← hι a b (sb_of_pos e), hw.2 a b e, map_zero]⟩
  refine ⟨ι f, hwf, hgen, fun M _ _ act' hL' J _ φ x hφ hu => ?_⟩
  let V : Submodule ℂ A := cycK ρ f
  let ρV : Ix r s → Ix r s → Module.End ℂ V := fun a b =>
    if h : sameBlock a b then (ρ a b).restrict (kSt_cycK ρ f a b h) else 0
  have hρV : ∀ a b, sameBlock a b → ∀ v : V, ((ρV a b v : V) : A) = ρ a b v := by
    intro a b h v
    simp only [ρV, dif_pos h]
    rfl
  let ιV : V →ₗ[ℂ] T := ι ∘ₗ V.subtype
  have hιV : ∀ a b, sameBlock a b → ∀ v, ιV (ρV a b v) = act (Eab a b) (ιV v) := by
    intro a b h v
    change ι ((ρV a b v : V) : A) = act (Eab a b) (ι (v : A))
    rw [hρV a b h, hι a b h]
  have hadjV : AdjK ρV := by
    intro a b h u v
    rw [Submodule.coe_inner, Submodule.coe_inner, hρV a b h, hρV b a (sameBlock_symm' h)]
    exact hadj a b h _ _
  set c0 : ℝ := ((casW La : ℚ) : ℝ) with hc0
  have hcc : (c0 : ℂ) = ((casW La : ℚ) : ℂ) := by simp [hc0]
  have hcV : casK ρV = (c0 : ℂ) • (1 : Module.End ℂ V) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have h1 := casK_intertw (ρ := ρV) (ρ' := ρ) V.subtype (fun a b h v => hρV a b h v) v
    change ((casK ρV v : V) : A) = (c0 : ℂ) • (v : A)
    rw [hcc, ← cas_cyc hgl hw v v.2]
    exact h1
  have hsV : StarK act (LinearMap.range ιV) c0 := by
    intro t ht x hx
    refine hs t ht x (Submodule.span_mono ?_ hx)
    rintro y ⟨a, b, hab, v, ⟨w, rfl⟩, rfl⟩
    exact ⟨a, b, hab, _, ⟨(w : A), rfl⟩, rfl⟩
  obtain ⟨hinj, hfin⟩ := cas_bound_gl act hL ρV hadjV c0 hcV ιV hιV hsV
  have hfV : f ∈ V := self_mem_cycK ρ f
  have hG : genG act (LinearMap.range ιV) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine genG_le' ?_ (genG_stable' _ _)
    rw [Submodule.span_singleton_le_iff_mem]
    exact le_genG' _ _ ⟨⟨f, hfV⟩, rfl⟩
  rw [hG] at hinj hfin
  have hVK : KSt (units act) (LinearMap.range ιV) := by
    rintro a b e _ ⟨v, rfl⟩
    exact ⟨_, hιV a b e v⟩
  have hp : ∀ i, ∃ p : ℂ[X], p.eval (c0 : ℂ) ≠ 0 ∧ aeval (casK (units act)) p (x i) ∈ LinearMap.range ιV := fun i => by
    obtain ⟨F, hF, hxF, hFK⟩ := hfin (x i) trivial
    have hCF : ∀ y ∈ F, casK (units act) y ∈ F := fun y hy => casK_mem hFK hy
    obtain ⟨p, hp1, hp2⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℂ ((casK (units act)).restrict hCF)
    refine poly_step _ _ _ (fun y => hinj y trivial) _ _ p rfl hp1.ne_zero ?_
    have := aeval_int (C := (casK (units act)).restrict hCF) (C' := casK (units act)) F.subtype (fun _ => rfl) p ⟨x i, hxF⟩
    rw [hp2] at this
    rw [show aeval (casK (units act)) p (x i) = _ from this.symm]
    simp
  choose p hp1 hp2 using hp
  have hP : ∀ i, aeval (casK (units act)) (∏ j, p j) (x i) ∈ LinearMap.range ιV := fun i => by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, Module.End.mul_apply]
    exact aeval_mem (fun y hy => casK_mem hVK hy) _ (hp2 i)
  have hP0 : (∏ j, p j).eval (c0 : ℂ) ≠ 0 := by
    rw [eval_prod]; exact Finset.prod_ne_zero_iff.2 fun j _ => hp1 j
  set u := ∑ i, φ i (x i) with hu0
  have hcu : casK (units act') u = (c0 : ℂ) • u := by rw [hcc]; exact cas_hw (glK_of_lie hL') hu
  have e1 : (∏ j, p j).eval (c0 : ℂ) • u = ∑ i, φ i (aeval (casK (units act)) (∏ j, p j) (x i)) := by
    rw [← Module.End.aeval_apply_of_mem_apply_eq_smul hcu, hu0, map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      (aeval_int (φ i) (casK_intertw (φ i) fun a b _ v => hφ i _ v) _ _).symm
  have hL1 : Lie (one act) := fun X Y => hL (X ()) (Y ())
  have hun : ∀ {N : Type} [AddCommGroup N] [Module ℂ N] (a' : Mat r s →ₗ[ℂ] Module.End ℂ N) (w : Unit) (a b : Ix r s),
      one a' (un w a b) = units a' a b := fun _ _ _ _ => rfl
  obtain ⟨W, hW1, hW2, hW3⟩ := cyc_le hL1 (sb := sameBlock) (pos := posC) (z := fun _ _ => False) (fun _ _ _ => sb_trans) sb_refl
    (fun _ _ => sb_of_pos) hD (fun _ _ e => (hD_pos e).le) (fun _ _ e => e.elim)
    (fun a b e e' => Or.inl ((sb_tri e).imp_right fun x => x.resolve_right fun y => (hD_pos y).not_ge e'))
    (Λ := fun _ a => (La a : ℂ)) (f := ι f) (fun _ a => hwf.1 a) (fun _ a b e => hwf.2 a b e)
    (Submodule.mem_span_singleton_self _) (fun _ _ _ e => e.elim)
  have hVW : LinearMap.range ιV ≤ W := by
    rintro _ ⟨v, rfl⟩
    have : V ≤ W.comap ι := sInf_le ⟨hW1, fun a b e y hy => by
      rw [Submodule.mem_comap, hι a b e]; exact hW3 _ (un_mem () e) _ hy⟩
    exact this v.2
  have hd := fun i => Submodule.mem_sup.1 (hW2 (hVW (hP i)))
  choose y hy z hz hyz using hd
  choose c hc using fun i => Submodule.mem_span_singleton.1 (hy i)
  set lam : ℂ := ∑ _w : Unit, ∑ a, hD a * (La a : ℂ)
  have e2 : (∏ j, p j).eval (c0 : ℂ) • u - ∑ i, c i • φ i (ι f) = ∑ i, φ i (z i) := by
    rw [e1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← hyz i, ← hc i, map_add, map_smul, add_sub_cancel_left]
  have e3 : ∑ i, φ i (z i) = 0 := by
    refine low_eig (T := one act' (dg Unit hD)) (lam := lam)
      (Submodule.sum_mem _ fun i _ => low_map (φ i) (fun v => hφ i _ v) (hz i)) ?_
    rw [← e2]
    refine sub_mem (Submodule.smul_mem _ _ (dg_hw (act := one act') hD (Λ := fun _ a => (La a : ℂ)) fun _ a => hu.1 a))
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (dg_hw (act := one act') hD (Λ := fun _ a => (La a : ℂ)) fun _ a => ?_))
    change act' (Eab a a) _ = _
    rw [← hφ, show act (Eab a a) (ι f) = _ from hwf.1 a, map_smul]
  rw [e3, sub_eq_zero] at e2
  refine ⟨fun i => ((∏ j, p j).eval (c0 : ℂ))⁻¹ * c i, ?_⟩
  rw [Finset.sum_congr rfl fun i _ => mul_smul _ (c i) (φ i (ι f)), ← Finset.smul_sum, ← e2, inv_smul_smul₀ hP0]

structure HWMod {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (act : (ι → Mat r s) →ₗ[ℂ] Module.End ℂ M) (Λ : ι → Ix r s → ℂ) (f : M) : Prop where
  lie : Lie act
  wt : ∀ w a, act (un w a a) f = Λ w a • f
  pos : ∀ w a b, posC a b → act (un w a b) f = 0
  gen : ∀ W : Submodule ℂ M, f ∈ W → St act ⊤ W → W = ⊤
  one : ∀ u, (∀ w a, act (un w a a) u = Λ w a • u) → (∀ w a b, posC a b → act (un w a b) u = 0) → ∃ c : ℂ, u = c • f

open GlobalTheory.RealLift in
theorem atPl_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L : Module.End ℂ (V w)) (y : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ y) = PiTensorProduct.tprod ℂ (Function.update y w (L (y w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases e : i = w
  · subst e; simp
  · simp [Function.update_of_ne e]

open GlobalTheory.RealLift in
theorem sumPl_single {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [AddCommGroup P] [Module ℂ P]
    (aP : ι → Mat r s →ₗ[ℂ] Module.End ℂ P) (w : ι) (Y : Mat r s) (y : ι → P) :
    sumPl (V := fun _ => P) (fun i => aP i ((Pi.single w Y : ι → Mat r s) i)) (PiTensorProduct.tprod ℂ y) =
      PiTensorProduct.tprod ℂ (Function.update y w (aP w Y (y w))) := by
  rw [sumPl, LinearMap.sum_apply, Finset.sum_eq_single w, atPl_tprod, Pi.single_eq_same]
  · intro i _ e
    rw [atPl_tprod, Pi.single_eq_of_ne e, map_zero, LinearMap.zero_apply, MultilinearMap.map_update_zero]
  · simp

open GlobalTheory.RealLift in
theorem tens_hw {ι P M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup P] [Module ℂ P] [AddCommGroup M] [Module ℂ M]
    {T : ι → Type} [∀ w, AddCommGroup (T w)] [∀ w, Module ℂ (T w)] (La : ι → Ix r s → ℚ)
    (aT : ∀ w, Mat r s →ₗ[ℂ] Module.End ℂ (T w)) (hS : ∀ w, Side (La w) (T w) (aT w))
    (aP : ι → Mat r s →ₗ[ℂ] Module.End ℂ P) (hP : ∀ w, IsLie (aP w)) (mk : ∀ w, P →ₗ[ℂ] T w)
    (hmk : ∀ w, Function.Surjective (mk w)) (hmka : ∀ w Y y, mk w (aP w Y y) = aT w Y (mk w y))
    (q : (⨂[ℂ] _ : ι, P) →ₗ[ℂ] M) (hq : Function.Surjective q)
    (hk : ∀ w y x, mk w x = 0 → q (PiTensorProduct.tprod ℂ (Function.update y w x)) = 0)
    (act : (ι → Mat r s) →ₗ[ℂ] Module.End ℂ M)
    (ha : ∀ Y t, act Y (q t) = q (sumPl (V := fun _ => P) (fun i => aP i (Y i)) t)) :
    ∃ f, HWMod act (fun w a => (La w a : ℂ)) f := by
  classical
  choose f0 hf1 hf2 hf3 using fun w => side_one (hS w)
  choose f hf using fun w => hmk w (f0 w)
  have a1 : ∀ w Y y, act (Pi.single w Y) (q (PiTensorProduct.tprod ℂ y)) =
      q (PiTensorProduct.tprod ℂ (Function.update y w (aP w Y (y w)))) := fun w Y y => by rw [ha, sumPl_single]
  have ext : ∀ {A B : Module.End ℂ M}, (∀ y, A (q (PiTensorProduct.tprod ℂ y)) = B (q (PiTensorProduct.tprod ℂ y))) → A = B := by
    intro A B h
    have : A ∘ₗ q = B ∘ₗ q := PiTensorProduct.ext (MultilinearMap.ext h)
    refine LinearMap.ext fun m => ?_
    obtain ⟨t, rfl⟩ := hq m
    exact LinearMap.congr_fun this t
  have sl : ∀ w y, ∃ φ : T w →ₗ[ℂ] M, ∀ x, φ (mk w x) = q (PiTensorProduct.tprod ℂ (Function.update y w x)) := fun w y =>
    exists_factor (mk w) (hmk w) (q ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap y w) fun x hx => hk w y x hx
  choose φ hφ using sl
  have hφa : ∀ w y Y x, φ w y (aT w Y x) = act (Pi.single w Y) (φ w y x) := fun w y Y x => by
    obtain ⟨x, rfl⟩ := hmk w x
    rw [← hmka, hφ, hφ, a1, Function.update_idem, Function.update_self]
  have hφ0 : ∀ w y, q (PiTensorProduct.tprod ℂ y) = φ w y (mk w (y w)) := fun w y => by rw [hφ, Function.update_eq_self]
  have L1 : ∀ w w' X Y, act (Pi.single w X) * act (Pi.single w' Y) - act (Pi.single w' Y) * act (Pi.single w X) =
      act (Pi.single w X * Pi.single w' Y - Pi.single w' Y * Pi.single w X) := by
    intro w w' X Y
    refine ext fun y => ?_
    by_cases e : w = w'
    · subst e
      rw [← Pi.single_mul, ← Pi.single_mul, ← Pi.single_sub, hφ0 w y, ← hφa, ← (hS w).1 X Y]
      simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hφa]
    · have z : ∀ {a b : ι} (U V : Mat r s), a ≠ b → (Pi.single a U * Pi.single b V : ι → Mat r s) = 0 := fun {a b} U V h => by
        funext i
        by_cases h' : i = a
        · subst h'; simp [Pi.single_eq_of_ne h]
        · simp [Pi.single_eq_of_ne h']
      rw [z _ _ e, z _ _ (Ne.symm e), sub_zero, map_zero, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        a1, a1, a1, a1, Function.update_of_ne e, Function.update_of_ne (Ne.symm e), Function.update_comm e, sub_self,
        LinearMap.zero_apply]
  have hL : Lie act := by
    intro X Y
    rw [← Finset.univ_sum_single X, ← Finset.univ_sum_single Y]
    simp only [map_sum, Finset.sum_mul_sum, map_sub]
    rw [Finset.sum_comm (f := fun i j => act (Pi.single i (Y i)) * act (Pi.single j (X j))),
      Finset.sum_comm (f := fun i j => act ((Pi.single i (Y i) : ι → Mat r s) * (Pi.single j (X j) : ι → Mat r s))), ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [L1, map_sub]
  refine ⟨q (PiTensorProduct.tprod ℂ f), hL, fun w a => ?_, fun w a b e => ?_, fun W hW hs => ?_, fun u h1 h2 => ?_⟩
  · rw [hφ0 w, un, ← hφa, hf, show aT w (Matrix.single a a 1) (f0 w) = _ from (hf1 w).1 a, map_smul]
  · rw [hφ0 w, un, ← hφa, hf, show aT w (Matrix.single a b 1) (f0 w) = _ from (hf1 w).2 a b e, map_zero]
  · have key : ∀ S : Finset ι, ∀ y, (∀ i ∉ S, y i = f i) → q (PiTensorProduct.tprod ℂ y) ∈ W := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro y hy; rw [show y = f from funext fun i => hy i (by simp)]; exact hW
      | insert w S hw ih =>
        intro y hy
        have : genG (aT w) (Submodule.span ℂ {f0 w}) ≤ W.comap (φ w y) := by
          refine genG_le' ?_ fun Y x hx => ?_
          · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap, ← hf, hφ]
            refine ih _ fun i hi => ?_
            by_cases e : i = w
            · subst e; simp
            · rw [Function.update_of_ne e]; exact hy i (by simp [e, hi])
          · rw [Submodule.mem_comap, hφa]; exact hs _ trivial _ hx
        rw [hf2] at this
        rw [hφ0 w]
        exact this trivial
    rw [eq_top_iff]
    intro m _
    obtain ⟨t, rfl⟩ := hq m
    have : (⊤ : Submodule ℂ (⨂[ℂ] _ : ι, P)) ≤ W.comap q := by
      rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      exact key Finset.univ y fun i hi => absurd (Finset.mem_univ i) hi
    exact this trivial
  · have key : ∀ S : Finset ι, u ∈ Submodule.span ℂ {m | ∃ y, (∀ i ∈ S, y i = f i) ∧ m = q (PiTensorProduct.tprod ℂ y)} := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        obtain ⟨t, rfl⟩ := hq u
        have : (⊤ : Submodule ℂ (⨂[ℂ] _ : ι, P)) ≤ (Submodule.span ℂ
            {m | ∃ y, (∀ i ∈ (∅ : Finset ι), y i = f i) ∧ m = q (PiTensorProduct.tprod ℂ y)}).comap q := by
          rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
          rintro _ ⟨y, rfl⟩
          exact Submodule.subset_span ⟨y, by simp, rfl⟩
        exact this trivial
      | insert w S hw ih =>
        obtain ⟨n, c, g, e⟩ := Submodule.mem_span_set'.1 ih
        choose y hy hy' using fun i => (g i).2
        have e' : ∑ i, φ w (y i) (c i • mk w (y i w)) = u := by
          rw [← e]; exact Finset.sum_congr rfl fun i _ => by rw [map_smul, ← hφ0, hy']
        obtain ⟨c', hc'⟩ := hf3 w M (act ∘ₗ LinearMap.single ℂ (fun _ => Mat r s) w)
          (fun X Y => by
            have := L1 w w X Y
            rwa [← Pi.single_mul, ← Pi.single_mul, ← Pi.single_sub] at this)
          (Fin n) (fun i => φ w (y i)) (fun i => c i • mk w (y i w)) (fun i Y x => hφa w (y i) Y x)
          (by rw [e']; exact ⟨fun a => h1 w a, fun a b h => h2 w a b h⟩)
        rw [← e', hc']
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, by rw [← hf, hφ]⟩)
        intro j hj
        by_cases e : j = w
        · subst e; simp
        · rw [Function.update_of_ne e]; exact hy i j ((Finset.mem_insert.1 hj).resolve_left e)
    have : Submodule.span ℂ {m | ∃ y, (∀ i ∈ (Finset.univ : Finset ι), y i = f i) ∧ m = q (PiTensorProduct.tprod ℂ y)} ≤
        Submodule.span ℂ {q (PiTensorProduct.tprod ℂ f)} := Submodule.span_mono (by
      rintro _ ⟨y, hy, rfl⟩
      rw [show y = f from funext fun i => hy i (Finset.mem_univ i)]
      rfl)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (this (key Finset.univ))
    exact ⟨c, hc.symm⟩

end PositivityTheory.ThKG.CayleyTransformDarboux

end
