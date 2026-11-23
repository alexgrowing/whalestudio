import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FinD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.CentFin

open MulAction UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Tf

section

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] {B : Base Γ G V} {s : B.Tw} {f : G → ℂ}

private noncomputable def FF (s : B.Tw) (f : G → ℂ) (δ : Γ) (y : G ⧸ B.U) : ℂ := s.ker f δ y * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ)

private theorem ker_mk (hf : s.IsTest f) (δ : Γ) (g : G) : s.ker f δ g = f (g⁻¹ * B.ι δ * s.θ g) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U g
  unfold Base.Tw.ker
  rw [hu]
  have e : (g * (u : G))⁻¹ * B.ι δ * s.θ (g * u) = ((u⁻¹ : B.U) : G) * (g⁻¹ * B.ι δ * s.θ g * s.θ u) := by
    simp only [map_mul, mul_inv_rev, Subgroup.coe_inv, mul_assoc]
  rw [e, hf.left, hf.right, map_inv]
  simp

private theorem FF_tr (δ : Γ) (y : G ⧸ B.U) : FF s f δ y = LinearMap.trace ℂ V (Tk s f y.out y.out (s.θΓ.symm δ)) := by
  unfold FF Tk Base.Tw.ker
  have hθ : s.θ (B.ι (s.θΓ.symm δ) * Quotient.out y) = B.ι δ * s.θ (Quotient.out y) := by
    rw [map_mul, s.comm, MulEquiv.apply_symm_apply]
  have hL : s.Θ ∘ₗ B.W (s.θΓ.symm δ) = B.W δ ∘ₗ s.Θ := by
    ext v
    simp [s.int]
  rw [hθ, hL, map_smul, smul_eq_mul]
  simp only [mul_assoc]

private theorem cusp_function_invariant (hf : s.IsTest f) (δ : Γ) (y : G ⧸ B.U) {z : Γ} (hz : z ∈ B.Γ₀) : FF s f (δ * z) y = FF s f δ y := by
  set u : B.U := ⟨B.ι z, B.memU z hz⟩ with hu
  have hθz : s.θ (B.ι z) = B.ι z := by rw [s.comm, s.fix z hz]
  have hc : B.ι z * s.θ (Quotient.out y) = s.θ (Quotient.out y) * B.ι z :=
    (Subgroup.mem_center_iff.mp (B.cenG z hz) _).symm
  have hk : s.ker f (δ * z) y = ((B.ω u)⁻¹ : ℂˣ) * s.ker f δ y := by
    unfold Base.Tw.ker
    have e : (Quotient.out y)⁻¹ * B.ι (δ * z) * s.θ (Quotient.out y) =
        ((Quotient.out y)⁻¹ * B.ι δ * s.θ (Quotient.out y)) * s.θ (u : G) := by
      rw [map_mul, show (u : G) = B.ι z from rfl, hθz]
      simp only [mul_assoc, hc]
    rw [e, hf.right]
  have ht : LinearMap.trace ℂ V (B.W (δ * z) ∘ₗ s.Θ) = (B.ω u : ℂ) * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) := by
    have hW : B.W (δ * z) ∘ₗ s.Θ = (B.ω u : ℂ) • (B.W δ ∘ₗ s.Θ) := by
      ext v
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, B.scal z hz, LinearMap.smul_apply, map_smul]
      rfl
    rw [hW, map_smul, smul_eq_mul]
  unfold FF
  rw [hk, ht, mul_mul_mul_comm, Units.inv_mul, one_mul]

private theorem ker_conj (hf : s.IsTest f) (δ x : Γ) (y : G ⧸ B.U) : s.ker f δ (B.ι x • y) = s.ker f (x⁻¹ * δ * s.θΓ x) y := by
  have hy : B.ι x • y = ((B.ι x * Quotient.out y : G) : G ⧸ B.U) := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  rw [hy, ker_mk hf]
  unfold Base.Tw.ker
  simp only [mul_inv_rev, map_mul, map_inv, s.comm, mul_assoc]

private theorem FF_conj [FiniteDimensional ℂ V] (hf : s.IsTest f) (δ x : Γ) (y : G ⧸ B.U) :
    FF s f δ (B.ι x • y) = FF s f (x⁻¹ * δ * s.θΓ x) y := by
  unfold FF
  rw [ker_conj hf]
  congr 1
  have e : B.W (x⁻¹ * δ * s.θΓ x) ∘ₗ s.Θ = B.W x⁻¹ * ((B.W δ ∘ₗ s.Θ) * B.W x) := by
    ext v
    simp [map_mul, s.int]
  rw [e, LinearMap.trace_mul_comm, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

private theorem termC [FiniteDimensional ℂ V] (hB : B.Fin) (hf : s.IsTest f) (δ : Γ) : letI := act B
    s.term f δ = ∑ᶠ a : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent δ),
      (B.Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ * FF s f (a.2.out * δ * s.θΓ a.2.out⁻¹) a.1.out := by
  letI := act B
  haveI := normal0 B
  have hle : B.Γ₀ ≤ s.Cent δ := by
    intro z hz
    show ∃ w ∈ B.Γ₀, z⁻¹ * δ * s.θΓ z = δ * w
    refine ⟨1, B.Γ₀.one_mem, ?_⟩
    rw [s.fix z hz, mul_one, mul_assoc, (Subgroup.mem_center_iff.mp (B.cenΓ hz) δ), inv_mul_cancel_left]
  have hinv : ∀ h ∈ s.Cent δ, ∀ y : G ⧸ B.U, FF s f δ (h • y) = FF s f δ y := by
    intro h hh y
    obtain ⟨w, hw, hhw⟩ := hh
    show FF s f δ (B.ι h • y) = _
    rw [FF_conj hf, hhw, cusp_function_invariant hf δ y hw]
  have hfin : {b : orbitRel.Quotient (s.Cent δ) (G ⧸ B.U) | FF s f δ (Quotient.out b) ≠ 0}.Finite := by
    obtain ⟨S, hS⟩ := centFin Γ G V B hB s f hf δ
    refine (S.finite_toSet.image (fun g : G =>
      (Quotient.mk'' ((g : G ⧸ B.U)) : orbitRel.Quotient (s.Cent δ) (G ⧸ B.U)))).subset ?_
    intro b hb
    have hk : s.ker f δ (Quotient.out b) ≠ 0 := fun h0 => hb (by unfold FF; rw [h0, zero_mul])
    obtain ⟨t, s1, hs1, u, hu, hy⟩ := hS _ hk
    refine ⟨s1, hs1, ?_⟩
    rw [← Quotient.out_eq b]
    apply Quotient.sound
    show (s1 : G ⧸ B.U) ∈ MulAction.orbit (s.Cent δ) (Quotient.out b)
    refine ⟨t⁻¹, ?_⟩
    conv_lhs => rw [← QuotientGroup.out_eq' (Quotient.out b)]
    show ((B.ι ((t⁻¹ : s.Cent δ) : Γ) * Quotient.out (Quotient.out b) : G) : G ⧸ B.U) = s1
    rw [hy]
    apply QuotientGroup.eq.mpr
    have e : (B.ι ((t⁻¹ : s.Cent δ) : Γ) * ((B.ι.comp (s.Cent δ).subtype) t * s1 * u))⁻¹ * s1 = u⁻¹ := by
      simp [mul_assoc]
    rw [e]
    exact B.U.inv_mem hu
  obtain ⟨-, hC⟩ := countC B.Γ₀ (s.Cent δ) (triv0 B) hle (stab0 B hB) (FF s f δ) hinv hfin
  have lhs : (fun a : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent δ) =>
      (B.Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ * FF s f (a.2.out * δ * s.θΓ a.2.out⁻¹) a.1.out) =
      fun a => (B.Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • FF s f δ (a.2.out⁻¹ • a.1.out) := by
    funext a
    rw [smul_eq_mul]
    congr 1
    rw [show (a.2.out⁻¹ • a.1.out : G ⧸ B.U) = B.ι a.2.out⁻¹ • a.1.out from rfl, FF_conj hf, inv_inv]
  rw [lhs, hC]
  unfold Base.Tw.term gqOn gq
  rw [mul_comm, finsum_mul]
  apply finsum_congr
  intro b
  unfold FF
  rw [smul_eq_mul, div_eq_mul_inv]
  have key : ∀ n m : ℕ, n = m → s.ker f δ (Quotient.out b) * (n : ℂ)⁻¹ * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) =
      (m : ℂ)⁻¹ * (s.ker f δ (Quotient.out b) * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ)) := by
    intro n m h
    rw [h]
    ring
  apply key
  rw [← Subgroup.relIndex_subgroupOf inf_le_left, Subgroup.inf_subgroupOf_left]
  congr 1

end

private theorem trace_mul_re_nonneg_of_posSemidef {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]
    {B : Base Γ G V} {s : B.Tw} {f : G → ℂ} (hf : s.IsTest f) (ε : Γ) (y : G ⧸ B.U) {z : Γ}
    (hz : z ∈ B.Γ₀) : s.ker f (ε * z) y = ((B.ω ⟨B.ι z, B.memU z hz⟩)⁻¹ : ℂˣ) * s.ker f ε y := by
  have hθz : s.θ (B.ι z) = B.ι z := by rw [s.comm, s.fix z hz]
  have hc : B.ι z * s.θ (Quotient.out y) = s.θ (Quotient.out y) * B.ι z :=
    (Subgroup.mem_center_iff.mp (B.cenG z hz) _).symm
  unfold Base.Tw.ker
  have e : (Quotient.out y)⁻¹ * B.ι (ε * z) * s.θ (Quotient.out y) =
      ((Quotient.out y)⁻¹ * B.ι ε * s.θ (Quotient.out y)) * s.θ ((⟨B.ι z, B.memU z hz⟩ : B.U) : G) := by
    rw [map_mul, show ((⟨B.ι z, B.memU z hz⟩ : B.U) : G) = B.ι z from rfl, hθz]
    simp only [mul_assoc, hc]
  rw [e, hf.right]

private theorem sum_phi_add_star_eq_trace {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]
    {B : Base Γ G V} (s : B.Tw) (δ₀ x : Γ) :
    ∃ w ∈ B.Γ₀, Quotient.out (x : Γ ⧸ s.Cent δ₀) * δ₀ * s.θΓ (Quotient.out (x : Γ ⧸ s.Cent δ₀))⁻¹ =
      x * δ₀ * s.θΓ x⁻¹ * w := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (s.Cent δ₀) x
  obtain ⟨z, hz, hcz⟩ := c.2
  have hzc : ∀ g : Γ, g * z⁻¹ = z⁻¹ * g := fun g =>
    Subgroup.mem_center_iff.mp (B.cenΓ (B.Γ₀.inv_mem hz)) g
  refine ⟨z⁻¹, B.Γ₀.inv_mem hz, ?_⟩
  have key : (c : Γ) * δ₀ * s.θΓ (c : Γ)⁻¹ = δ₀ * z⁻¹ := by
    rw [map_inv, mul_inv_eq_iff_eq_mul]
    have h1 : δ₀ * s.θΓ c = c * (δ₀ * z) := by
      rw [← hcz]
      group
    calc (c : Γ) * δ₀ = c * (δ₀ * z) * z⁻¹ := by group
      _ = δ₀ * s.θΓ c * z⁻¹ := by rw [h1]
      _ = δ₀ * z⁻¹ * s.θΓ c := by rw [mul_assoc, hzc, ← mul_assoc]
  rw [hc]
  calc x * (c : Γ) * δ₀ * s.θΓ (x * c)⁻¹ = x * ((c : Γ) * δ₀ * s.θΓ (c : Γ)⁻¹) * s.θΓ x⁻¹ := by
        rw [mul_inv_rev, map_mul]
        group
    _ = x * δ₀ * s.θΓ x⁻¹ * z⁻¹ := by
        rw [key]
        simp only [mul_assoc, hzc (s.θΓ x⁻¹)]

theorem UpperTheory.V.Z.Sym.Tf.trace :
    UpperTheory.V.Z.Sym.Tf.Trace := by
  intro Γ G V _ _ _ _ _ B hB s f hf I δ hinj hcov
  letI := act B
  haveI := finQ B hB
  have hHD : HD s f := finD B hB s f hf
  have hzc : ∀ z ∈ B.Γ₀, ∀ g : Γ, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (B.cenΓ hz) g
  let e : (i : I) → Γ ⧸ s.Cent (δ i) → Γ := fun i a => Quotient.out a * δ i * s.θΓ (Quotient.out a)⁻¹
  let m : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) →
      orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) :=
    fun p => (p.2.1, (((s.θΓ.symm (e p.1 p.2.2))⁻¹ : Γ) : Γ ⧸ B.Γ₀))
  let ε : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) → Γ := fun b => s.θΓ (Quotient.out b.2)⁻¹
  have K1 : ∀ p, ∃ w ∈ B.Γ₀, ε (m p) = e p.1 p.2.2 * w := by
    intro p
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul B.Γ₀ ((s.θΓ.symm (e p.1 p.2.2))⁻¹)
    refine ⟨(w : Γ)⁻¹, B.Γ₀.inv_mem w.2, ?_⟩
    show s.θΓ (Quotient.out ((((s.θΓ.symm (e p.1 p.2.2))⁻¹ : Γ)) : Γ ⧸ B.Γ₀))⁻¹ = _
    rw [hw, mul_inv_rev, inv_inv, map_mul, MulEquiv.apply_symm_apply, map_inv, s.fix _ w.2]
    exact (hzc _ (B.Γ₀.inv_mem w.2) _).symm
  have Minj : Function.Injective m := by
    rintro ⟨i, o, a⟩ ⟨i', o', a'⟩ h
    have ho : o = o' := congrArg Prod.fst h
    have ha : (((s.θΓ.symm (e i a))⁻¹ : Γ) : Γ ⧸ B.Γ₀) = (((s.θΓ.symm (e i' a'))⁻¹ : Γ) : Γ ⧸ B.Γ₀) :=
      congrArg Prod.snd h
    have hu : s.θΓ.symm (e i a) * (s.θΓ.symm (e i' a'))⁻¹ ∈ B.Γ₀ := by
      have := QuotientGroup.eq.mp ha
      rwa [inv_inv] at this
    have hfix := s.fix _ hu
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hfix
    obtain ⟨z, hz, hEz⟩ : ∃ z ∈ B.Γ₀, e i' a' = e i a * z := by
      refine ⟨(s.θΓ.symm (e i a) * (s.θΓ.symm (e i' a'))⁻¹)⁻¹, B.Γ₀.inv_mem hu, ?_⟩
      rw [hzc _ (B.Γ₀.inv_mem hu) (e i a), ← hfix]
      group
    have h2 : Quotient.out a' * δ i' * s.θΓ (Quotient.out a')⁻¹ =
        Quotient.out a * δ i * s.θΓ (Quotient.out a)⁻¹ * z := hEz
    have gen : ∀ d d' q q' : Γ, q' * d' * s.θΓ q'⁻¹ = q * d * s.θΓ q⁻¹ * z →
        d' = (q⁻¹ * q')⁻¹ * d * s.θΓ (q⁻¹ * q') * z := by
      intro d d' q q' hq
      have h3 : d' = q'⁻¹ * (q * d * s.θΓ q⁻¹ * z) * s.θΓ q' := by
        rw [← hq, map_inv]
        group
      calc d' = q'⁻¹ * (q * d * (s.θΓ q)⁻¹) * (z * s.θΓ q') := by
            rw [h3, map_inv]
            group
        _ = q'⁻¹ * (q * d * (s.θΓ q)⁻¹) * (s.θΓ q' * z) := by rw [← hzc z hz (s.θΓ q')]
        _ = _ := by
            rw [map_mul, map_inv]
            group
    have hx := gen _ _ _ _ h2
    have hii := hinj i i' ⟨_, z, hz, hx⟩
    subst hii
    have hcent : (Quotient.out a)⁻¹ * Quotient.out a' ∈ s.Cent (δ i) :=
      ⟨z⁻¹, B.Γ₀.inv_mem hz, eq_mul_inv_of_mul_eq hx.symm⟩
    have haa : a = a' := by
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' a']
      exact QuotientGroup.eq.mpr hcent
    rw [ho, haa]
  let F' : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) → ℂ := fun b =>
    (B.Γ₀.relIndex (stabilizer Γ (Quotient.out b.1)) : ℂ)⁻¹ *
      LinearMap.trace ℂ V (Tk s f (Quotient.out (Quotient.out b.1)) (Quotient.out (Quotient.out b.1))
        (Quotient.out b.2)⁻¹)
  let F : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) → ℂ := fun p =>
    (B.Γ₀.relIndex (stabilizer Γ (Quotient.out p.2.1)) : ℂ)⁻¹ * FF s f (e p.1 p.2.2) (Quotient.out p.2.1)
  have hF'FF : ∀ b, F' b = (B.Γ₀.relIndex (stabilizer Γ (Quotient.out b.1)) : ℂ)⁻¹ *
      FF s f (ε b) (Quotient.out b.1) := by
    intro b
    show _ * _ = _ * FF s f (s.θΓ (Quotient.out b.2)⁻¹) _
    rw [FF_tr, MulEquiv.symm_apply_apply]
  have hFeq : ∀ p, F p = ((((fun _ => 1) : _ → ℕ) (m p) : ℕ) : ℂ)⁻¹ • F' (m p) := by
    intro p
    rw [Nat.cast_one, inv_one, one_smul, hF'FF]
    obtain ⟨w, hw, hwe⟩ := K1 p
    rw [hwe, cusp_function_invariant hf _ _ hw]
  have hKfin : {b : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) | s.ker f (ε b) (Quotient.out b.1) ≠ 0}.Finite := by
    refine (Set.finite_iUnion (fun o : orbitRel.Quotient Γ (G ⧸ B.U) =>
      (Set.finite_singleton o).prod (f_fin hHD (Quotient.out (Quotient.out o)) (Quotient.out (Quotient.out o))))).subset ?_
    rintro ⟨o, x⟩ hb
    have hb' : f ((Quotient.out (Quotient.out o))⁻¹ * B.ι (s.θΓ (Quotient.out x)⁻¹) *
        s.θ (Quotient.out (Quotient.out o))) ≠ 0 := hb
    refine Set.mem_iUnion.mpr ⟨o, Set.mem_singleton o, ?_⟩
    show f _ ≠ 0
    convert hb' using 2
    rw [map_mul, s.comm, mul_assoc]
  have hF'fin : (Function.support F').Finite := hKfin.subset (fun b hb h0 => hb (by
    rw [hF'FF]
    unfold FF
    rw [h0]
    ring))
  have Msurj : ∀ b, s.ker f (ε b) (Quotient.out b.1) ≠ 0 → ∃ p, m p = b := by
    rintro ⟨o, x⟩ hb
    obtain ⟨i, y, z, hz, hy⟩ := hcov _ ⟨_, hb⟩
    refine ⟨⟨i, o, ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i))⟩, ?_⟩
    obtain ⟨w, hw, hwe⟩ := sum_phi_add_star_eq_trace s (δ i) y⁻¹
    have hy' : s.θΓ (Quotient.out x)⁻¹ = y⁻¹ * δ i * s.θΓ y * z := hy
    have hE : e i ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i)) = s.θΓ (Quotient.out x)⁻¹ * (z⁻¹ * w) := by
      show Quotient.out _ * δ i * s.θΓ (Quotient.out _)⁻¹ = _
      rw [hwe, inv_inv, hy']
      group
    have hsym : ∀ q ∈ B.Γ₀, s.θΓ.symm q = q := fun q hq =>
      (MulEquiv.symm_apply_eq _).mpr (s.fix q hq).symm
    have hzw : z⁻¹ * w ∈ B.Γ₀ := B.Γ₀.mul_mem (B.Γ₀.inv_mem hz) hw
    refine Prod.ext rfl ?_
    show (((s.θΓ.symm (e i ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i))))⁻¹ : Γ) : Γ ⧸ B.Γ₀) = x
    rw [← QuotientGroup.out_eq' x, QuotientGroup.eq, inv_inv, hE, map_mul, MulEquiv.symm_apply_apply,
      hsym _ hzw, mul_assoc, ← hzc _ hzw (Quotient.out x), ← mul_assoc, inv_mul_cancel, one_mul]
    exact hzw
  have hcard : ∀ b, F' b ≠ 0 → ((fun _ => 1) : _ → ℕ) b ≠ 0 ∧
      Nat.card {p // m p = b} = ((fun _ => 1) : _ → ℕ) b := by
    intro b hb
    refine ⟨one_ne_zero, Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun p q => Subtype.ext (Minj (p.2.trans q.2.symm))⟩, ?_⟩⟩
    have hk : s.ker f (ε b) (Quotient.out b.1) ≠ 0 := fun h0 => hb (by
      rw [hF'FF]
      unfold FF
      rw [h0]
      ring)
    obtain ⟨p, hp⟩ := Msurj b hk
    exact ⟨⟨p, hp⟩⟩
  obtain ⟨hFfin, hsum⟩ := sum_fib m F F' (fun _ => 1) hF'fin hcard hFeq
  refine ⟨?_, ?_⟩
  · have hP : {p : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) |
        s.ker f (e p.1 p.2.2) (Quotient.out p.2.1) ≠ 0} ⊆
        m ⁻¹' {b | s.ker f (ε b) (Quotient.out b.1) ≠ 0} := by
      intro p hp
      obtain ⟨w, hw, hwe⟩ := K1 p
      show s.ker f (ε (m p)) (Quotient.out (m p).1) ≠ 0
      rw [hwe, trace_mul_re_nonneg_of_posSemidef hf _ _ hw]
      exact mul_ne_zero (Units.ne_zero _) hp
    have hPfin := (hKfin.preimage Minj.injOn).subset hP
    refine (hPfin.image Sigma.fst).subset ?_
    rintro i ⟨y, hy⟩
    obtain ⟨g, hg⟩ : ∃ g : Γ, g • y = Quotient.out (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U)) :=
      Quotient.mk_out (s := orbitRel Γ (G ⧸ B.U)) y
    refine ⟨⟨i, (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U)), ((g : Γ) : Γ ⧸ s.Cent (δ i))⟩, ?_, rfl⟩
    obtain ⟨w, hw, hwe⟩ := sum_phi_add_star_eq_trace s (δ i) g
    show s.ker f (e i ((g : Γ) : Γ ⧸ s.Cent (δ i))) (Quotient.out (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U))) ≠ 0
    rw [show e i ((g : Γ) : Γ ⧸ s.Cent (δ i)) = _ from hwe, trace_mul_re_nonneg_of_posSemidef hf _ _ hw]
    refine mul_ne_zero (Units.ne_zero _) ?_
    rw [← hg, show g • y = B.ι g • y from rfl, ker_conj hf]
    convert hy using 2
    rw [map_inv]
    group
  · rw [traceA hB hf hHD]
    calc _ = ∑ᶠ (a : orbitRel.Quotient Γ (G ⧸ B.U)) (b : Γ ⧸ B.Γ₀), F' (a, b) := rfl
      _ = ∑ᶠ ab, F' ab := (finsum_curry F' hF'fin).symm
      _ = ∑ᶠ p, F p := hsum.symm
      _ = ∑ᶠ (i : I) (q : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))), F ⟨i, q⟩ := finsum_sig F hFfin
      _ = ∑ᶠ i, s.term f (δ i) := finsum_congr fun i => (termC hB hf (δ i)).symm
