import Formalism.SharpRestriction.Divisibility.BoundaryLocalData

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField Formalism.MainNotions

def integersConjugation (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

theorem integers_conjugation_coe (D : D7) (c : 𝓞 D.host.E) : ((integersConjugation D c : 𝓞 D.host.E) : D.host.E) = D.host.conj (c : D.host.E) := rfl

def XT (_D : D7) (Y : Type) : Type := Y

instance (D : D7) (Y : Type) [AddCommGroup Y] : AddCommGroup (XT D Y) := inferInstanceAs (AddCommGroup Y)

instance (D : D7) (Y : Type) [AddCommGroup Y] [Module (𝓞 D.host.E) Y] : Module (𝓞 D.host.E) (XT D Y) :=
  Module.compHom Y (integersConjugation D)

def XT.mk (D : D7) (Y : Type) [AddCommGroup Y] : Y ≃+ XT D Y := AddEquiv.refl Y

theorem XT.smul_mk (D : D7) {Y : Type} [AddCommGroup Y] [Module (𝓞 D.host.E) Y] (c : 𝓞 D.host.E) (a : Y) :
    c • XT.mk D Y a = XT.mk D Y (integersConjugation D c • a) := rfl

theorem XT.symm_smul (D : D7) {Y : Type} [AddCommGroup Y] [Module (𝓞 D.host.E) Y] (c : 𝓞 D.host.E) (χ : XT D Y) :
    (XT.mk D Y).symm (c • χ) = integersConjugation D c • (XT.mk D Y).symm χ := rfl

def vHom (p : ℕ) (C : Type) [NormedField C] : Additive Cˣ →+ ℝ where
  toFun u := BoundaryLocalData.vU p (Additive.toMul u)
  map_zero' := by simp [BoundaryLocalData.vU]
  map_add' u v := by
    simp only [BoundaryLocalData.vU, toMul_add, Units.val_mul, norm_mul]
    rw [Real.logb_mul (by simp) (by simp)]
    ring

theorem exists_section (p : ℕ) {C : Type} [NormedField C] (M : Submodule ℤ ℝ) [Module.Finite ℤ M]
    (hM : ∀ m ∈ M, ∃ u : Additive Cˣ, vHom p C u = m) :
    ∃ s : M →ₗ[ℤ] Additive Cˣ, ∀ m : M, vHom p C (s m) = m := by
  classical
  haveI : Module.Free ℤ M := by
    first
    | exact Module.free_of_finite_type_torsion_free'
    | infer_instance
  let b := Module.Free.chooseBasis ℤ M
  choose u hu using fun i => hM _ (b i).2
  refine ⟨b.constr ℤ u, fun m => ?_⟩
  have key : (vHom p C).toIntLinearMap ∘ₗ b.constr ℤ u = M.subtype :=
    b.ext fun i => by simp [hu]
  simpa using LinearMap.congr_fun key m

theorem exists_tau (p : ℕ) {C : Type} [NormedField C] {Y : Type} [AddCommGroup Y] [Module.Finite ℤ Y]
    (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (h : ∀ a b, ∃ u : Cˣ, β a b = BoundaryLocalData.vU p u) :
    ∃ t : Y → Y → Cˣ, (∀ a a' b, t (a + a') b = t a b * t a' b) ∧ (∀ a b b', t a (b + b') = t a b * t a b') ∧
      (∀ a b a' b', β a b = β a' b' → t a b = t a' b') ∧ ∀ a b, β a b = BoundaryLocalData.vU p (t a b) := by
  classical
  have key : ∀ x : TensorProduct ℤ Y Y, ∃ u : Additive Cˣ, vHom p C u = TensorProduct.lift β x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul a b =>
      obtain ⟨u, hu⟩ := h a b
      exact ⟨Additive.ofMul u, by rw [TensorProduct.lift.tmul, hu]; rfl⟩
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      exact ⟨u + v, by rw [map_add, map_add, hu, hv]⟩
  have hM : ∀ m ∈ LinearMap.range (TensorProduct.lift β), ∃ u : Additive Cˣ, vHom p C u = m := by
    rintro m ⟨x, rfl⟩
    exact key x
  obtain ⟨s, hs⟩ := exists_section (C := C) p _ hM
  have mem : ∀ a b, β a b ∈ LinearMap.range (TensorProduct.lift β) :=
    fun a b => ⟨a ⊗ₜ b, TensorProduct.lift.tmul _ _⟩
  refine ⟨fun a b => Additive.toMul (s ⟨β a b, mem a b⟩), ?_, ?_, ?_, ?_⟩
  · intro a a' b
    have e : (⟨β (a + a') b, mem _ _⟩ : LinearMap.range (TensorProduct.lift β)) =
        ⟨β a b, mem a b⟩ + ⟨β a' b, mem a' b⟩ := Subtype.ext (by simp)
    show Additive.toMul (s ⟨β (a + a') b, mem _ _⟩) =
      Additive.toMul (s ⟨β a b, mem a b⟩) * Additive.toMul (s ⟨β a' b, mem a' b⟩)
    first
    | (rw [e, map_add]; rfl)
    | (rw [e, map_add, toMul_add])
    | (simp only [e, map_add]; rfl)
  · intro a b b'
    have e : (⟨β a (b + b'), mem _ _⟩ : LinearMap.range (TensorProduct.lift β)) =
        ⟨β a b, mem a b⟩ + ⟨β a b', mem a b'⟩ := Subtype.ext (by simp)
    show Additive.toMul (s ⟨β a (b + b'), mem _ _⟩) =
      Additive.toMul (s ⟨β a b, mem a b⟩) * Additive.toMul (s ⟨β a b', mem a b'⟩)
    first
    | (rw [e, map_add]; rfl)
    | (rw [e, map_add, toMul_add])
    | (simp only [e, map_add]; rfl)
  · intro a b a' b' hab
    have e : (⟨β a b, mem a b⟩ : LinearMap.range (TensorProduct.lift β)) = ⟨β a' b', mem a' b'⟩ :=
      Subtype.ext hab
    show Additive.toMul (s ⟨β a b, mem a b⟩) = Additive.toMul (s ⟨β a' b', mem a' b'⟩)
    rw [e]
  · intro a b
    show β a b = BoundaryLocalData.vU p (Additive.toMul (s ⟨β a b, mem a b⟩))
    have hab := (hs ⟨β a b, mem a b⟩).symm
    first
    | exact hab
    | (simp only [vHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hab; exact hab)
    | (rw [hab]; rfl)

theorem exists_lin {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] {v : V}
    (hv : v ≠ 0) (w : W) : ∃ f : V →ₗ[K] W, f v = w := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hv
    first
    | exact (Module.forall_dual_apply_eq_zero_iff K v).1 hc
    | exact (Module.forall_dual_apply_eq_zero_iff v).1 hc
  refine ⟨(φ v)⁻¹ • φ.smulRight w, ?_⟩
  simp [LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ]

theorem exists_alp (D : D7) (p n : ℕ) (h : ModuliIntegralCharts.NHyp D p n) : ∃ α : 𝓞 D.host.E,
    (α : D.host.E) * D.host.conj (α : D.host.E) = (n : D.host.E) ∧
    ((∃ mm : ℕ, n = mm ^ 2 ∧ α = (mm : 𝓞 D.host.E)) ∨ (α : D.host.E) ∈ D.host.K) := by
  obtain ⟨-, -, h⟩ := h
  rcases h with ⟨mm, rfl⟩ | ⟨π, hK, hπ⟩
  · refine ⟨(mm : 𝓞 D.host.E), ?_, Or.inl ⟨mm, rfl, rfl⟩⟩
    have h1 : ((mm : 𝓞 D.host.E) : D.host.E) = (mm : D.host.E) := by
      first
      | simp
      | norm_cast
    rw [h1, map_natCast]
    push_cast
    ring
  · exact ⟨π, hπ, Or.inr hK⟩

structure LocBHyp (D : D7) {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) : Prop where

  be_val : ∀ (Z : L.Mdl) (y : L.Pt Z) (a b : L.Ylat y), ∃ u : ((L.fld y).C)ˣ, L.be y a b = BoundaryLocalData.vU p u

  psiV_val : ∀ (Z : L.Mdl) (y : L.Pt Z) (a : L.Ylat y), ∃ u : ((L.fld y).C)ˣ, L.psiV y a = BoundaryLocalData.vU p u

  oX : ∃ O : L.Sh L.Xm, L.IsInv O ∧ ∀ (F : L.Sh L.Xm) (φ : L.GIso O F), ∃ s : L.Sec F,
    ∀ y, L.nrm F s y = (p : ℝ) ^ (-(L.vrat φ y))

  keySh_inv : L.IsInv L.piPP → ∀ c, L.IsInv (L.keySh c)

  dP_le : ∀ y : L.Pt L.Xm, L.dP y ≤ D.R.f * r

  th_ne : ∀ y nW, (∃ s : L.Sn y (L.latStd nW) 1, s ≠ 0) ∨
    ∀ n, ModuliIntegralCharts.NHyp D p n → L.vth y (L.latStd nW) n = 0

  intJet_free : ∀ y nW n DF, ∃ (N : ℕ) (b : Module.Basis (Fin N) (L.fld y).C (L.Jet y (L.latStd nW) n DF)),
    ∀ v, v ∈ L.intJet y (L.latStd nW) n DF ↔ ∀ i, ‖b.repr v i‖ ≤ 1

theorem locBHyp_of_LocB {D : D7} {r j p : ℕ} {L : ModuliIntegralCharts.Loc D r j p} (B : BoundaryLocalData.LocB D L) : LocBHyp D L where
  be_val := fun _ y a b => ⟨B.tau y a (B.phi y b), B.be_tau y a b⟩
  psiV_val := fun _ y a => ⟨B.mulC y a (BoundaryLocalData.w0 D • a), B.psiV_def y a⟩
  oX := ⟨B.oX, B.oX_inv, fun _ φ => ⟨B.secOf φ, B.nrm_secOf φ⟩⟩
  keySh_inv := B.keySh_inv
  dP_le := fun y => by have := B.dimB_add y; omega
  th_ne := fun y nW => by
    by_cases h : B.th1 y nW = 0
    · exact Or.inr fun n hn => by rw [B.vth_def y nW n hn, h, map_zero]
    · exact Or.inl ⟨_, h⟩
  intJet_free := B.intJet_free

theorem nonempty_boundary_local_trivial_biext (D : D7) {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) (H : LocBHyp D L) :
    Nonempty (BoundaryLocalData.LocB D L) := by
  classical
  have h1 := fun (Z : L.Mdl) (y : L.Pt Z) => exists_tau p (L.be y) (H.be_val Z y)
  choose t t1 t2 t3 t4 using h1
  choose u hu using H.psiV_val
  obtain ⟨O, hO, hsec⟩ := H.oX
  choose sec hsec using hsec
  have h2 : ∀ y nW, ∃ th : L.Sn y (L.latStd nW) 1, ∀ n,
      ∃ f : L.Sn y (L.latStd nW) 1 →ₗ[(L.fld y).C] L.Sn y (L.latStd nW) n,
        ModuliIntegralCharts.NHyp D p n → L.vth y (L.latStd nW) n = f th := by
    intro y nW
    rcases H.th_ne y nW with ⟨s, hs⟩ | h0
    · refine ⟨s, fun n => ?_⟩
      obtain ⟨f, hf⟩ := exists_lin (K := (L.fld y).C) hs (L.vth y (L.latStd nW) n)
      exact ⟨f, fun _ => hf.symm⟩
    · exact ⟨0, fun n => ⟨0, fun hn => by simpa using h0 n hn⟩⟩
  choose th pb hpb using h2
  exact ⟨{
    chX := fun {Z} y => XT D (L.Ylat y)
    xAdd := fun {Z} y => inferInstance
    xMod := fun {Z} y => inferInstance
    phi := fun {Z} y => XT.mk D (L.Ylat y)
    phi_conj := fun {Z} y c c' h a => by
      have : c' = integersConjugation D c := RingOfIntegers.ext (by rw [h, integers_conjugation_coe])
      rw [this, XT.smul_mk]
    tau := fun {Z} y a χ => t Z y a ((XT.mk D (L.Ylat y)).symm χ)
    tau_add_left := fun {Z} y a a' χ => t1 Z y a a' _
    tau_add_right := fun {Z} y a χ χ' => by rw [map_add]; exact t2 Z y a _ _
    tau_symm := fun {Z} y a b => t3 Z y _ _ _ _ (L.be_symm y a b)
    tau_smul := fun {Z} y c a χ => by
      rw [XT.symm_smul]
      exact t3 Z y _ _ _ _ (L.be_bal y c (integersConjugation D c) (integers_conjugation_coe D c) a _)
    be_tau := fun {Z} y a b => t4 Z y a b
    multiplicationLatticeFirst := fun {Z} y _ _ => 0
    multiplicationLatticeSecond := fun {Z} y _ _ => 0
    mulC := fun {Z} y a _ => u Z y a
    psiV_def := fun {Z} y a => hu Z y a
    StrictHenselianAcyclic := L.LBG
    squareRootLineBundle := L.LBGq
    res2 := fun {La} P => L.resQ P
    PoiQ := L.PPq
    biext := fun {La} _ => True
    dg := fun {La} P => P
    dgq := fun {La} P => P
    dg_res := fun {La} P => rfl
    PPq_def := fun La => rfl
    BPt := Empty
    Rl := fun z => z.elim
    iRr := fun z => z.elim
    iRd := fun z => z.elim
    iRl := fun z => z.elim
    iRn := fun z => z.elim
    iRi := fun z => z.elim
    iRc := fun z => z.elim
    Yb := fun z => z.elim
    iYa := fun z => z.elim
    iYm := fun z => z.elim
    Xb := fun z => z.elim
    iXa := fun z => z.elim
    iXm := fun z => z.elim
    phib := fun z => z.elim
    phib_conj := fun z => z.elim
    taub := fun z => z.elim
    taub_add_left := fun z => z.elim
    taub_add_right := fun z => z.elim
    taub_symm := fun z => z.elim
    taub_smul := fun z => z.elim
    taub_pos := fun z => z.elim
    Sg := fun z => z.elim
    iSg := fun z => z.elim
    iSk := fun z => z.elim
    iSm := fun z => z.elim
    iSt := fun z => z.elim
    Sreg := fun z => z.elim
    fc := fun z => z.elim
    trU := fun z => z.elim
    oX := O
    oX_inv := hO
    secOf := fun {F} φ => sec F φ
    nrm_secOf := fun {F} φ y => hsec F φ y
    keySh_inv := H.keySh_inv
    dimB := fun y => D.R.f * r - L.dP y
    dimB_add := fun y => Nat.sub_add_cancel (H.dP_le y)
    FB := fun y nW n _ => L.Sn y (L.latStd nW) n
    fbAdd := fun y nW n _ => inferInstanceAs (AddCommGroup (L.Sn y (L.latStd nW) n))
    fbMod := fun y nW n _ => inferInstanceAs (Module (L.fld y).C (L.Sn y (L.latStd nW) n))
    nB := fun {y nW n χ} _ => 2
    sgc := fun y nW n χ => if χ = 0 then LinearMap.id else 0
    trB := fun y nW n a χ => LinearEquiv.refl _ _
    trB_norm := fun y nW n a χ σ => rfl
    alp := fun n => if h : ModuliIntegralCharts.NHyp D p n then (exists_alp D p n h).choose else 0
    alp_spec := fun n h => by
      rw [dif_pos h]
      exact (exists_alp D p n h).choose_spec
    th1 := th
    pbAl := pb
    vth_def := fun y nW n hn => hpb y nW n hn
    jX := fun y nW n DF χ => L.jet y (L.latStd nW) n DF
    intJet_free := H.intJet_free
    jX_int := fun y nW n DF χ σ h => absurd h (by norm_num)
    jet_fourier := fun y nW n DF s c hc => by
      refine ⟨{0}, fun F hF => ⟨0, zero_mem _, ?_⟩⟩
      have h0 : (0 : Fin nW → XT D (L.Ylat y)) ∈ F := hF (Finset.mem_singleton_self 0)
      rw [Finset.sum_eq_single_of_mem 0 h0 (fun χ _ hχ => by simp [hχ])]
      simp }⟩

theorem nonempty_boundary_local_iff (D : D7) {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) :
    Nonempty (BoundaryLocalData.LocB D L) ↔ LocBHyp D L :=
  ⟨fun ⟨B⟩ => locBHyp_of_LocB B, nonempty_boundary_local_trivial_biext D L⟩

theorem locBHyp_of_isEmpty (D : D7) {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) (hP : ∀ Z, IsEmpty (L.Pt Z))
    (O : L.Sh L.Xm) (hO : L.IsInv O) (hk : L.IsInv L.piPP → ∀ c, L.IsInv (L.keySh c)) : LocBHyp D L where
  be_val := fun Z y => (hP Z).elim y
  psiV_val := fun Z y => (hP Z).elim y
  oX := ⟨O, hO, fun _ _ => ⟨0, fun y => (hP _).elim y⟩⟩
  keySh_inv := hk
  dP_le := fun y => (hP _).elim y
  th_ne := fun y => (hP _).elim y
  intJet_free := fun y => (hP _).elim y

end Formalism.MainNotions.DIV.Inh

end
