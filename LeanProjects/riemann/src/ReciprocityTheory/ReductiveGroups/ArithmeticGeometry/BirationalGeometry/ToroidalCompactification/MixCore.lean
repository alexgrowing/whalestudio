import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThMonoidFirstComponent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem twist_of_val {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ} {M : LB A.left}
    (hM : M.IsLB) {α : LB.Gen (LB.LinComb M (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen)
    {s : LB.Sec (LPow A M b T)} {s' : LB.Sec (LPow A M a T)} (h : ∀ z J, Good M z J →
      sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) z J =
      (val α (𝟙 _) z J).val * sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) z J) :
    IsTwistPull A M ψ m hm a b α s s' := fun j => fn_ext fun z hz => by
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hM (χ z)
  have hz' : (𝟙 (T ⊗ A).left : _ ⟶ _) z ∈ LB.wchart M ![(snd T A).left, m.left] j := hz
  have a₁ := (gs_res (𝟙 _) z (chart_le_zero A M m j) hz' (s'.f fun _ => j 0)).trans
    (sec_trans (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) z (chart_le_zero A M m j hz')
      (Good.mem hJ _ _))
  have a₂ := ((gs_res (𝟙 _) z (chart_le_pull A M ψ m hm j) hz' ((ψ.left.app _).hom (s.f fun _ => j 1))).trans
    (gs_pull (𝟙 _) ψ.left z (LB.wchart M (fun _ : Fin 1 => (snd T A).left) fun _ => j 1) (chart_le_pull A M ψ m hm j hz') _)).trans
    (sec_trans (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) z
      (chart_le_pull A M ψ m hm j hz') (Good.mem hJ _ _))
  have a₃ := (gs_unit (𝟙 _) z _ hz' (α.s j)).trans (congrArg Units.val (gen_trans hα (𝟙 _) z hz' (Good.mem hJ _ _)))
  refine a₁.trans (Eq.trans ?_ ((gs_mul (𝟙 _) z _ hz' _ _).trans (congrArg₂ (· * ·) a₃ a₂)).symm)
  refine (congrArg (_ * ·) (h z J hJ)).trans ?_
  have e : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, ← Over.comp_left, hm]
  have t : trF (L := M) (K := Fin 2) ![(snd T A).left, m.left] ![a, -b] (𝟙 _) z j
        (fun k => J (𝟙 _ ≫ (![(snd T A).left, m.left] : Fin 2 → _) k)) *
      trF (L := M) (fun _ : Fin 1 => (snd T A).left) (fun _ => b) (𝟙 _ ≫ ψ.left) z (fun _ => j 1)
        (fun _ => J ((𝟙 _ ≫ ψ.left) ≫ (snd T A).left)) =
      trF (L := M) (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (𝟙 _) z (fun _ => j 0) (fun _ => J (𝟙 _ ≫ (snd T A).left)) := by
    rw [trF, trF, trF, Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one, e]
    exact (_root_.mul_assoc _ _ _).trans ((congrArg (_ * ·) ((congrArg (· * _) (zpow_neg _ _)).trans (inv_mul_cancel _))).trans
      (_root_.mul_one _))
  rw [← t, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]
  rfl

variable [IsCommMonObj A] {L : RigLB A}

theorem isMonHom_mulA (n : ℕ) : IsMonHom (mulA A n) where
  one_hom := by
    have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by simp [Hom.one_def]
    rw [mulA, MonObj.comp_pow, Category.comp_id, e, one_pow]
  mul_hom := by
    have e : μ[A] = fst A A * snd A A := by simp [Hom.mul_def]
    rw [mulA, MonObj.comp_pow, Category.comp_id]
    conv_lhs => rw [e, mul_pow]
    rw [e, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id]

def EndPull (L : RigLB A) (φ : A ⟶ A) (a b : ℤ) {T : Over S} (s : LB.Sec (LPow A L.L b T)) (s' : LB.Sec (LPow A L.L a T)) : Prop :=
  ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![a, -b])),
    α₀.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (eSec A))
      (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b))) ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (lift (fst T A) (snd T A ≫ φ)) (snd T A ≫ φ) (lift_snd _ _) a b α s s'

def MixedOver (L : RigLB A) (φ : A ⟶ A) (n k : ℕ) {T : Over S} (ok : (T ⟶ A) → Prop) (s : LB.Sec (LPow A L.L 1 T))
    (t₁ b : T ⟶ A) (hh : LB.Sec (LPow A L.L (k : ℤ) T)) : Prop :=
  ∃ (F₁ : LB.Sec (LPow A L.L ((n : ℤ) ^ 2) T))
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (h₁ : LB.Sec (LPow A L.L (k : ℤ) T)) (U : ThetaGrp A L.L (k : ℤ) T),
    VtOver L n ok s t₁ F₁ ∧ α₀.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (eSec A))
      (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig (k : ℤ)) (rigPow A L.L L.rig (-((n : ℤ) ^ 2)))) ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (lift (fst T A) (snd T A ≫ φ)) (snd T A ≫ φ) (lift_snd _ _) (k : ℤ) ((n : ℤ) ^ 2) α F₁ h₁ ∧
    SymLift A L.L (k : ℤ) k b U ∧ IsActOf A L.L (k : ℤ) U h₁ hh

omit [IsCommMonObj A] [GrpObj A] in
theorem prod_end (φ : A ⟶ A) {a b : ℕ} {a' b' : ℤ} (ha : a' = a) (hb : b' = b) {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U]
    (h : (T.left ⟶ A.left) → U) : ∏ i, h (y.left ≫ (![𝟙 A.left, φ.left] : Fin 2 → _) i) ^ (![a', -b'] : Fin 2 → ℤ) i =
      h y.left ^ a * (h (y ≫ φ).left ^ b)⁻¹ := by
  subst ha hb
  rw [Fin.prod_univ_two]
  simp [Over.comp_left, zpow_neg, zpow_natCast]

set_option maxHeartbeats 4000000 in
theorem mix_core (c : CubicalStr A L) (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hsym : L.IsSymmetric) {g n M : ℕ}
    (hM : M = g * n) (hN : Odd M) (p q f f' : A ⟶ A) [IsMonHom p] [IsMonHom q] [IsMonHom f] [IsMonHom f']
    (hpq : q ≫ p = mulA A g) (hqp : p ≫ q = mulA A g) (cp : p ≫ f' = f' ≫ p) (cq : q ≫ f' = f' ≫ q) (hr : RosatiAdj A L.L f f')
    {T : Over S} (ok : (T ⟶ A) → Prop) (hf : ∀ x, ok x → x ≫ f = 1) (hg : ∀ x, ok x → x ≫ f' = x)
    (hk : ∀ x, ok x → x ^ (M ^ 2) = 1) (hK : ∀ W : ThetaGrp A L.L ((n : ℤ) ^ 2) T, W.pt ^ (n ^ 2) = 1)
    {s : LB.Sec (LPow A L.L 1 T)} {t t₁ b : T ⟶ A} {F : LB.Sec (LPow A L.L ((M : ℤ) ^ 2) T)}
    {hh : LB.Sec (LPow A L.L ((g * n ^ 2 : ℕ) : ℤ) T)} (hb : ok b) (hbq : b ≫ q = 1) (ht : t = (b ≫ p) ^ n * t₁)
    (hF : VtOver L M ok s t F) (hH : MixedOver L p n (g * n ^ 2) ok s t₁ b hh) :
    EndPull L q ((M : ℤ) ^ 2) ((g * n ^ 2 : ℕ) : ℤ) hh F := by
  obtain ⟨_, β, βT, s₁, U, htU, oU, gβ, nβ, cβ, twβ, slU, acU⟩ := hF
  obtain ⟨F₁, α, αT, h₁, Ub, ⟨_, β', βT', s₁', U₁, ht₁, o₁, gβ', nβ', cβ', twβ', sl₁, ac₁⟩, gα, nα, cα, twα, slb, acb⟩ := hH
  obtain rfl := slU.pt_eq
  obtain rfl := sl₁.pt_eq
  obtain rfl := slb.pt_eq
  have := isMonHom_mulA (A := A) n
  have cM : ((M : ℤ) ^ 2) = ((M ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  have cn : ((n : ℤ) ^ 2) = ((n ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  have mul : ∀ {T : Over S} (y : T ⟶ A) (k : ℕ), y ≫ mulA A k = y ^ k := fun y k => by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  have yqp : ∀ {T : Over S} (y : T ⟶ A), ((y ≫ q) ≫ p) ^ n = y ^ M := fun y => by
    rw [Category.assoc, hpq, mul, ← pow_mul, hM]
  obtain ⟨ga, gga, vga⟩ := exists_gen L.isLB (φ' := ![𝟙 A.left, q.left]) (ε' := ![(M : ℤ) ^ 2, -((g * n ^ 2 : ℕ) : ℤ)])
    (fun V _ h => by
      have e₁ := prod_mulN M (𝟙 A) h
      have e₂ := prod_end q cM rfl (𝟙 A) V h (b := g * n ^ 2)
      simp only [Over.id_left, Category.id_comp] at e₁ e₂
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 2 ⊕ Fin 2) (U := V) _ e₁ (prod_neg _ _ (prod_sum₂ (K := Fin 2) (K' := Fin 2)
        (U := V) _ (prod_end p rfl cn q V h) (prod_mulN n (q ≫ p) h)))).trans (Eq.trans ?_ e₂.symm)
      have := yqp (𝟙 A)
      rw [Category.id_comp] at this
      rw [this]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (LB.mulGen L.L _ _ _ _ β (LB.invGen L.L _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ α q.left)
        (LB.pullGen L.L _ _ β' (q ≫ p).left))))
    (mulGen_isGen _ _ _ _ _ _ _ gβ (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ gα _)
      (pullGen_isGen _ _ _ _ gβ' _))))
  have vga' : ∀ {Z : Scheme.{0}} (r : Z ⟶ A.left) z J, Good L.L z J → val ga r z J =
      val β r z J * (val α (r ≫ q.left) z J * val β' (r ≫ (q ≫ p).left) z J)⁻¹ := fun r z J hJ => by
    rw [vga _ r z J hJ, val_mul hJ, val_inv, val_mul hJ, val_pull hJ, val_pull hJ]
  obtain ⟨gaT, ggaT, vgaT⟩ := exists_gen L.isLB (φ' := ![(snd T A).left, (snd T A ≫ q).left])
    (ε' := ![(M : ℤ) ^ 2, -((g * n ^ 2 : ℕ) : ℤ)]) (fun V _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun r => h r ^ _) (Category.comp_id _)
      · rfl) (LB.pullGen L.L _ _ ga (snd T A).left) (pullGen_isGen _ _ _ _ gga _)
  refine ⟨ga, gaT, gga, corr_of_val L.isLB fun w I hI => ?_, corr_of_val L.isLB fun w I hI => vgaT _ _ w I hI,
    twist_of_val L.isLB ggaT fun z J hJ => ?_⟩
  · have rp : ∀ k : ℤ, val (rigPow A L.L L.rig k) (𝟙 _) w I =
        val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (𝟙 _) w I ^ k := fun k => map_zpow _ _ _
    have b₁ := (val_pull hI _ _ _).symm.trans ((val_corr hI nβ (𝟙 _)).trans ((val_mul hI _ _ _).trans
      (congrArg₂ (· * ·) (rp _) (val_inv _ _))))
    have b₂ := (val_pull hI _ _ _).symm.trans ((val_corr hI nβ' (𝟙 _)).trans ((val_mul hI _ _ _).trans
      (congrArg₂ (· * ·) (rp _) (val_inv _ _))))
    have b₃ := (val_pull hI _ _ _).symm.trans ((val_corr hI nα (𝟙 _)).trans ((val_mul hI _ _ _).trans
      (congrArg₂ (· * ·) (rp _) (rp _))))
    have e : ∀ (r : A ⟶ A) [IsMonHom r], (𝟙 _ ≫ eSec A) ≫ r.left = 𝟙 _ ≫ eSec A := fun r _ =>
      (Category.assoc _ _ _).trans (congrArg (fun x : 𝟙_ (Over S) ⟶ A => 𝟙 _ ≫ x.left) (IsMonHom.one_hom r))
    refine ((val_pull hI _ _ _).trans (vga' _ w I hI)).trans (Eq.trans ?_ ((val_mul hI _ _ _).trans
      (congrArg₂ (· * ·) (rp _) (rp _))).symm)
    rw [e q, e (q ≫ p), b₁, b₂, b₃]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  have C : IsCub (cubV c (T := T ⊗ A) z J) := isCub_cubV c hJ
  obtain ⟨u, hu, nu⟩ := exists_ros hG hA L.isLB f f' hr
  obtain ⟨-, ws, gws, -⟩ := hsym
  obtain ⟨ν₀, hν₀⟩ := gen_of_iso ((isGen_iff ws).1 gws) (𝟙 A.left)
  have hν := invGen_isGen _ _ _ _ hν₀
  have Fν : ∀ {T : Over S} (y : T ⟶ A) (V : Type) [CommGroup V] (h : (T.left ⟶ A.left) → V),
      ∏ i, h (y.left ≫ (![𝟙 A.left ≫ (GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) i) ^ (-(![1, -1] : Fin 2 → ℤ) i) =
        h y.left * (h y⁻¹.left)⁻¹ := fun y V _ h => by
    rw [Fin.prod_univ_two]
    show h (y.left ≫ 𝟙 _ ≫ _) ^ (-1 : ℤ) * h (y.left ≫ 𝟙 _) ^ (- -1 : ℤ) = _
    rw [Category.id_comp, Category.comp_id, neg_neg, zpow_one, zpow_neg_one, mul_comm]; rfl
  let σ := fst T A
  have pk : ∀ {x : T ⟶ A} {k : ℕ}, x ^ k = 1 → (σ ≫ x) ^ k = 1 := fun h => by rw [← MonObj.comp_pow, h, MonObj.comp_one]
  have k₁ := hK U₁
  have kb : Ub.pt ^ (g * n ^ 2) = 1 := by
    rw [pow_mul, ← mul _ g, ← hpq, ← Category.assoc, hbq, MonObj.one_comp, one_pow]
  let v : T ⟶ A := Ub.pt⁻¹ * (U.pt ≫ q)
  let d : T ⟶ A := U₁.pt⁻¹ * (v ≫ p)
  have vp : (v ≫ p) ^ n = U₁.pt ^ n := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, mul_pow, inv_pow, yqp, htU, ht, inv_mul_cancel_left, ht₁]
  have dn : d ^ n = 1 := by rw [mul_pow, inv_pow, vp, inv_mul_cancel]
  have dn2 : d ^ (n ^ 2) = 1 := by rw [pow_two, pow_mul, dn, one_pow]
  have vk : v ^ (g * n ^ 2) = 1 := by
    rw [pow_mul, ← mul _ g, ← hqp, ← Category.assoc, ← MonObj.pow_comp, pow_two, pow_mul, vp, ← pow_mul, ← pow_two, k₁,
      MonObj.one_comp]
  have vg : v ≫ f' = v := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hg _ hb, Category.assoc, cq, ← Category.assoc, hg _ oU]
  have dg : d ≫ f' = d := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hg _ o₁, Category.assoc, cp, ← Category.assoc, vg]
  have dv₁ : n ^ 2 ∣ M ^ 2 := pow_dvd_pow_of_dvd ⟨g, by rw [hM, mul_comm]⟩ 2
  have dv₂ : g * n ^ 2 ∣ M ^ 2 := ⟨g, by rw [hM]; ring⟩
  have pw : ∀ {x : T ⟶ A} {k : ℕ}, x ^ k = 1 → k ∣ M ^ 2 → (σ ≫ x) ^ (M ^ 2) = 1 := fun h ⟨r, hr⟩ => by
    rw [hr, pow_mul, pk h, one_pow]
  obtain ⟨G₁, S₁⟩ := symLift_geo (σ := σ) hJ hG hA _ hν Fν cn sl₁ k₁
  obtain ⟨Gb, Sb⟩ := symLift_geo (σ := σ) hJ hG hA _ hν Fν rfl slb kb
  obtain ⟨GU, SU⟩ := symLift_geo (σ := σ) hJ hG hA _ hν Fν cM slU (hk _ oU)
  have Fβ' : ∀ {T : Over S} (y : T ⟶ A) (V : Type) [CommGroup V] (h : (T.left ⟶ A.left) → V),
      ∏ i, h (y.left ≫ (![𝟙 A.left, (mulA A n).left] : Fin 2 → _) i) ^ (![(n : ℤ) ^ 2, -1] : Fin 2 → ℤ) i =
        h y.left ^ (n ^ 2) * (h (y ≫ mulA A n).left ^ 1)⁻¹ := fun y V _ h => by rw [prod_mulN, mul, pow_one]
  have Gd := IsGeo.pull hJ (σ := σ) (x := d) (mulA A n) (a := 1) (g := 1) (by rw [mul, dn]; exact isGeo_one) β' gβ' Fβ'
  obtain ⟨κ₁, hκ₁⟩ := nu_pull hJ hG hA _ hν Fν (mulA A n) β' gβ' Fβ'
  have Sd := (Th.sym_one (N := M ^ 2) (ν := fun y : T ⊗ A ⟶ A => val (LB.invGen L.L _ _ ν₀) y.left z J ^ 1)).pull (MonoidHom.mk' (· ≫ mulA A n) fun a b => MonObj.mul_comp a b _)
    (fun y => val β' y.left z J) (x := σ ≫ d) (by show (σ ≫ d) ≫ _ = 1; rw [mul, pk dn]) (pw dn2 dv₁) hκ₁
  have i₁ := ros_pow' c hG hA f f' u hu nu hJ (x := σ ≫ d) (m := σ ≫ U₁.pt) (pk dn2) (pk k₁)
    (by rw [Category.assoc, hf _ o₁, MonObj.comp_one])
  rw [Category.assoc, dg] at i₁
  have S₂ := (S₁.of_dvd dv₁).mul Sd (Th.commute_of C (pk k₁) (pk dn2) (G₁.cub hJ c hG hA k₁) (Gd.cub hJ c hG hA dn2) i₁)
  have G₂ := G₁.mul hJ Gd
  rw [show U₁.pt * d = v ≫ p from mul_inv_cancel_left _ _] at G₂
  have G₃ := G₂.pull hJ p α gα (prod_end p rfl cn)
  obtain ⟨κ₂, hκ₂⟩ := nu_pull hJ hG hA _ hν Fν p α gα (prod_end p rfl cn)
  have S₃ := S₂.pull (MonoidHom.mk' (· ≫ p) fun a b => MonObj.mul_comp a b _) (fun y => val α y.left z J) (x := σ ≫ v)
    ((Category.assoc _ _ _).trans G₂.1.symm) (pw vk dv₂) hκ₂
  have i₂ := ros_pow' c hG hA f f' u hu nu hJ (x := σ ≫ v) (m := σ ≫ Ub.pt) (pk vk) (pk kb)
    (by rw [Category.assoc, hf _ hb, MonObj.comp_one])
  rw [Category.assoc, vg] at i₂
  have S₄ := (Sb.of_dvd dv₂).mul S₃ (Th.commute_of C (pk kb) (pk vk) (Gb.cub hJ c hG hA kb) (G₃.cub hJ c hG hA vk) i₂)
  have G₄ := Gb.mul hJ G₃
  rw [show Ub.pt * v = U.pt ≫ q from mul_inv_cancel_left _ _] at G₄
  have G₅ := G₄.pull hJ q ga gga (prod_end q cM rfl)
  obtain ⟨κ₃, hκ₃⟩ := nu_pull hJ hG hA _ hν Fν q ga gga (prod_end q cM rfl)
  have S₅ := S₄.pull (MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b _) (fun y => val ga y.left z J) (x := σ ≫ U.pt)
    ((Category.assoc _ _ _).trans G₄.1.symm) (pk (hk _ oU)) hκ₃
  have E := SU.unique (hN.pow (n := 2)) S₅ rfl (fun y => (GU.cub hJ c hG hA (hk _ oU) y).trans
    (((congrArg₂ (· * ·) rfl (eq_inv_mul_of_mul_eq (G₅.cub hJ c hG hA (hk _ oU) y).symm)).trans (_root_.mul_assoc _ _ _).symm)))
  have E₁ := congrArg (fun x => x.f (snd T A)) E
  have i₀ : (lift σ (snd T A)).left = 𝟙 _ := congrArg (fun x => x.left) (lift_fst_snd : lift (fst T A) (snd T A) = 𝟙 _)
  have va : ∀ {m : T ⊗ A ⟶ A} {φ : A ⟶ A} {e : Fin 2 → ℤ} {β₀ : LB.Gen (LB.LinComb L.L ![𝟙 A.left, φ.left] e)}
      {β : LB.Gen (LB.LinComb L.L ![(snd T A).left, m.left] e)}
      (_ : LB.Gen.Corr L.L _ _ _ _ β (LB.pullGen L.L _ _ β₀ (snd T A).left)) (y : T ⊗ A ⟶ A),
      val β (lift σ y).left z J = val β₀ y.left z J := fun h y =>
    (val_corr hJ h _).trans ((val_pull hJ _ _ _).trans (by rw [← Over.comp_left, lift_snd]))
  have mt : ∀ (k : ℕ) (y : T ⊗ A ⟶ A), (lift σ y).left ≫ (mulT A T k).left = (lift σ (y ^ k)).left := fun k y => by
    rw [← Over.comp_left, mulT, comp_lift, lift_fst, MonObj.comp_pow, lift_snd]
  have et : ∀ (r : A ⟶ A) (y : T ⊗ A ⟶ A), (lift σ y).left ≫ (lift (fst T A) (snd T A ≫ r)).left = (lift σ (y ≫ r)).left :=
    fun r y => by rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
  have w₁ := twist_val acU (lift σ (snd T A)).left z hJ
  rw [← Over.comp_left, lift_transl, twist_val twβ _ z hJ, mt, va cβ] at w₁
  have w₂ := twist_val acb (lift σ (snd T A ≫ q)).left z hJ
  rw [← Over.comp_left, lift_transl, twist_val twα _ z hJ, et, va cα] at w₂
  have w₃ := twist_val ac₁ (lift σ (((σ ≫ Ub.pt) * (snd T A ≫ q)) ≫ p)).left z hJ
  rw [← Over.comp_left, lift_transl, twist_val twβ' _ z hJ, mt, va cβ'] at w₃
  have pt : ((σ ≫ U₁.pt) * ((σ ≫ Ub.pt) * (snd T A ≫ q)) ≫ p) ^ n = ((σ ≫ U.pt) * snd T A) ^ M := by
    have cpw : ∀ (x : T ⟶ A) (k : ℕ), (σ ≫ x) ^ k = σ ≫ x ^ k := fun x k => by rw [MonObj.comp_pow]
    rw [MonObj.mul_comp, mul_pow, mul_pow, mul_pow, yqp, Category.assoc, cpw, cpw, cpw, htU, ht, ht₁, MonObj.comp_mul,
      ← _root_.mul_assoc, mul_comm (σ ≫ t₁)]
  rw [w₃, pt] at w₂
  rw [← i₀, et, w₁, w₂, vgaT _ _ z J hJ, val_pull hJ, ← Over.comp_left, lift_snd]
  simp only [← _root_.mul_assoc, ← Units.val_mul]
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
  have e₁ : (snd T A ≫ q) * (σ ≫ Ub.pt) * (σ ≫ v) = (snd T A * (σ ≫ U.pt)) ≫ q := by
    rw [_root_.mul_assoc, ← MonObj.comp_mul, mul_inv_cancel_left, MonObj.mul_comp, Category.assoc]
  have e₂ : ((snd T A ≫ q) * (σ ≫ Ub.pt)) ≫ p * (σ ≫ U₁.pt) * (σ ≫ d) = ((snd T A * (σ ≫ U.pt)) ≫ q) ≫ p := by
    rw [_root_.mul_assoc, ← MonObj.comp_mul, mul_inv_cancel_left, ← Category.assoc, ← MonObj.mul_comp, e₁]
  have g₁ := vga' (snd T A * (σ ≫ U.pt)).left z J hJ
  rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc] at g₁
  simp only [Th.pull, Th.mul_f, MonoidHom.mk'_apply, e₁, e₂, g₁] at E₁
  rw [mul_comm (σ ≫ U.pt), mul_comm (σ ≫ U₁.pt), mul_comm (σ ≫ Ub.pt)]
  refine (congrArg (· * _) E₁).trans (Additive.ofMul.injective ?_)
  have o : ∀ y, (1 : Th (T ⊗ A ⟶ A) ((T ⊗ A).left.presheaf.stalk z)ˣ).f y = 1 := fun _ => rfl
  simp only [o, ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem theta_pt_pow (c : CubicalStr A L) (hK : KTriv A L.L) {R : Type} [CommRing R] (t : Sp R ⟶ S) {k : ℕ} {kz : ℤ}
    (hk : kz = k) (W : ThetaGrp A L.L kz (Over.mk t)) : W.pt ^ k = 1 := by
  subst hk
  refine hK R t _ fun p => ?_
  obtain ⟨V, hV, v, hv⟩ := exists_local_gen L.isLB (K := Fin 3) ![(W.pt ^ k).left, (1 : Over.mk t ⟶ A).left, W.pt.left]
    ![1, (k : ℤ) - 1, -(k : ℤ)] p
  obtain ⟨u, hu, -⟩ := exists_cubN c (1 : Over.mk t ⊗ A ⟶ A) (fst _ A ≫ W.pt) (snd _ A) k
  let i := ((fst (Over.mk t) A).left ⁻¹ᵁ V).ι
  obtain ⟨w, hw, -⟩ := exists_gen L.isLB (φ' := fun j => i ≫ (![((fst _ A ≫ W.pt ^ k) * snd _ A).left, (snd _ A).left] :
      Fin 2 → _) j) (ε' := ![1, -1]) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 8 ⊕ Fin 2) (K' := Fin 3) (U := U) _ (prod_sum₂ (K := Fin 8) (K' := Fin 2) (U := U) _
        (Fin.prod_univ_eight _) (Fin.prod_univ_two _)) (Fin.prod_univ_three _)).trans ?_
      have e : ∀ q : Over.mk t ⟶ A, ((fst (Over.mk t) A).left ∣_ V) ≫ V.ι ≫ q.left = i ≫ (fst _ A ≫ q).left := fun q => by
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc]; rfl
      rw [Fin.prod_univ_two]
      simp only [Sum.elim_inr, Sum.elim_inl, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, e, translPt_eq,
        _root_.one_mul, MonObj.comp_one, MonObj.comp_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module) (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u i)
        (LB.pullGen L.L _ _ (LB.invGen L.L _ _ (thG W)) i)) (LB.pullGen L.L _ _ v ((fst (Over.mk t) A).left ∣_ V)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu _)
      (pullGen_isGen _ _ _ _ (invGen_isGen _ _ _ _ W.isGen) _)) (pullGen_isGen _ _ _ _ hv _))
  exact ⟨V, hV, gen_chartPull (chartPullOut L.L _ _ _ _ fun _ => rfl) w hw⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

set_option maxHeartbeats 800000 in

theorem mix_obj (hG : GlobalFnsSt) {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b₀ : Base l B} {s₀ : S ⟶ Sp B}
    (o : Obj D l b₀ s₀) {R : Type} [CommRing R] {x₀ : Sp R ⟶ S} {π : 𝓞 E} {g n : ℕ} (hπ : π * H.bar π = g) (hM : l.M = g * n)
    (hle : l.Mb ≤ Ideal.span {H.bar π}) {s : LB.Sec (LPow o.t.G o.t.PP.L 1 (Over.mk x₀))} {t t₁ b : Over.mk x₀ ⟶ o.t.G}
    {F : LB.Sec (LPow o.t.G o.t.PP.L ((l.M : ℤ) ^ 2) (Over.mk x₀))}
    {hh : LB.Sec (LPow o.t.G o.t.PP.L ((g * n ^ 2 : ℕ) : ℤ) (Over.mk x₀))}
    (hb : ∀ a ∈ Ideal.span {H.bar π}, b ≫ o.t.act.act a = 1) (ht : t = (b ≫ o.t.act.act π) ^ n * t₁)
    (hF : VtOver o.t.PP l.M (fun x => ∀ a ∈ l.Mb ^ 2, x ≫ o.t.act.act a = 1) s t F)
    (hH : MixedOver o.t.PP (o.t.act.act π) n (g * n ^ 2) (fun x => ∀ a ∈ l.Mb ^ 2, x ≫ o.t.act.act a = 1) s t₁ b hh) :
    EndPull o.t.PP (o.t.act.act (H.bar π)) ((l.M : ℤ) ^ 2) ((g * n ^ 2 : ℕ) : ℤ) hh F := by
  haveI := o.t.comm
  have hbb : ∀ a : 𝓞 E, H.bar (H.bar a) = a := fun a => by
    apply RingOfIntegers.ext
    show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  have h0 : o.t.act.act 0 = 1 := by simpa using o.t.act.add 0 0
  have hnat : ∀ k : ℕ, o.t.act.act (k : 𝓞 E) = mulA o.t.G k := by
    intro k
    induction k with
    | zero => simp only [Nat.cast_zero, h0, mulA, pow_zero]
    | succ k ih =>
      simp only [mulA] at ih ⊢
      rw [Nat.cast_succ, o.t.act.add, ih, o.t.act.one, pow_succ]
  have hA : IsAbelianScheme o.t.G := by
    have hp := o.proper
    obtain ⟨⟩ := o.t.semi
    constructor <;> assumption
  have htop : l.Mb ^ 2 ⊔ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2 = ⊤ :=
    Ideal.pow_sup_pow_eq_top l.coprime
  have h1mem : (1 : 𝓞 E) ∈ l.Mb ^ 2 ⊔ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2 := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨e, he, w, hw, hew⟩ := Submodule.mem_sup.mp h1mem
  have hw' : w ∈ (l.Mb ^ 2).map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [Ideal.map_pow]; exact hw
  obtain ⟨y, hy, hyw⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).mp hw'
  have hbw : H.bar w ∈ l.Mb ^ 2 := by
    rw [← hyw]
    show H.bar (H.bar y) ∈ _
    rw [hbb]; exact hy
  have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
    have hm : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf.trans inf_le_left) hm
  haveI := o.t.act.hom π
  haveI := o.t.act.hom (H.bar π)
  haveI := o.t.act.hom e
  haveI := o.t.act.hom (H.bar e)
  refine mix_core o.t.cub hG hA o.t.sym hM l.odd (o.t.act.act π) (o.t.act.act (H.bar π))
    (o.t.act.act e) (o.t.act.act (H.bar e)) ?_ ?_ ?_ ?_ (o.t.rosatiAdj e)
    (fun x => ∀ a ∈ l.Mb ^ 2, x ≫ o.t.act.act a = 1) ?_ ?_ ?_ ?_ ?_ ?_ ht hF hH
  · rw [← o.t.act.mul, mul_comm, hπ, hnat]
  · rw [← o.t.act.mul, hπ, hnat]
  · rw [← o.t.act.mul, ← o.t.act.mul, mul_comm]
  · rw [← o.t.act.mul, ← o.t.act.mul, mul_comm]
  · exact fun x hx => hx e he
  · intro x hx
    have h1 : o.t.act.act (H.bar e) * o.t.act.act (H.bar w) = 𝟙 _ := by
      rw [← o.t.act.add, ← map_add, hew, map_one, o.t.act.one]
    have h2 := congrArg (fun u => x ≫ u) h1
    simp only [comp_mul, hx _ hbw, _root_.mul_one, Category.comp_id] at h2
    exact h2
  · intro x hx
    have h3 := hx ((l.M ^ 2 : ℕ) : 𝓞 E) (by rw [Nat.cast_pow]; exact Ideal.pow_mem_pow hMb 2)
    rwa [hnat, mulA, comp_pow, Category.comp_id] at h3
  · exact fun W => theta_pt_pow o.t.cub o.ktriv x₀ (k := n ^ 2) (by simp) W
  · exact fun a ha => hb a (hle (Ideal.pow_le_self two_ne_zero ha))
  · exact hb _ (Ideal.mem_span_singleton_self _)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
