import ReciprocityTheory.DualLattices.NsmulTensorEqZero
import ReciprocityTheory.DualLattices.SmKerSurj
import ReciprocityTheory.DualLattices.TangentPairingStatement

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

abbrev Tot (R : LAlg R₀) : Type u := Σ x y : B.G R, B.P R x y

def Tmap {R S : LAlg R₀} (f : LHom R S) (t : B.Tot R) : B.Tot S :=
  ⟨B.map f t.1, B.map f t.2.1, B.pmap f t.2.2⟩

lemma tot_ext {R : LAlg R₀} {t t' : B.Tot R} (h1 : t.1 = t'.1) (h2 : t.2.1 = t'.2.1)
    (h3 : HEq t.2.2 t'.2.2) : t = t' := by
  rcases t with ⟨a, b, c⟩
  rcases t' with ⟨a', b', c'⟩
  dsimp only at h1 h2 h3
  subst h1
  subst h2
  cases h3
  rfl

lemma tot_eq {R : LAlg R₀} {t t' : B.Tot R} (h : t = t') :
    t.1 = t'.1 ∧ t.2.1 = t'.2.1 ∧ HEq t.2.2 t'.2.2 := by
  subst h
  exact ⟨rfl, rfl, HEq.rfl⟩

lemma Tmap_comp {R S T : LAlg R₀} (f : LHom R S) (g : LHom S T) (t : B.Tot R) :
    B.Tmap (g.comp f) t = B.Tmap g (B.Tmap f t) :=
  B.tot_ext (B.map_comp f g t.1) (B.map_comp f g t.2.1) (B.pmap_comp f g t.2.2)

def Tsw {R : LAlg R₀} (t : B.Tot R) : B.Tot R := ⟨t.2.1, t.1, B.sw t.2.2⟩

lemma Tmap_Tsw {R S : LAlg R₀} (f : LHom R S) (t : B.Tot R) :
    B.Tmap f (B.Tsw t) = B.Tsw (B.Tmap f t) :=
  B.tot_ext rfl rfl (heq_of_eq (B.sw_nat f t.2.2).symm)

def totalFibreNsmulSnd {R : LAlg R₀} (N : ℕ) (t : B.Tot R) : B.Tot R := ⟨t.1, N • t.2.1, B.nsmul2 t.2.2 N⟩

private lemma pmap_tr2_heq {R S : LAlg R₀} (f : LHom R S) {x y y' : B.G R} (h : y = y')
    (v : B.P R x y) : HEq (B.pmap f (B.tr2 h v)) (B.pmap f v) := by
  subst h
  exact HEq.rfl

private lemma tr2_heq {R : LAlg R₀} {x y y' : B.G R} (h : y = y') (v : B.P R x y) :
    HEq (B.tr2 h v) v := by
  subst h
  exact HEq.rfl

private lemma add2_heq_of_heq {R : LAlg R₀} {x y₁ y₂ z : B.G R} (h : y₁ = y₂) {a : B.P R x y₁}
    {a' : B.P R x y₂} (b : B.P R x z) (e : HEq a a') : HEq (B.add2 a b) (B.add2 a' b) := by
  subst h
  cases e
  exact HEq.rfl

private lemma pmap_nsmul2_heq {R S : LAlg R₀} (f : LHom R S) {x y : B.G R} (u : B.P R x y)
    (n : ℕ) : HEq (B.pmap f (B.nsmul2 u n)) (B.nsmul2 (B.pmap f u) n) := by
  induction n with
  | zero =>
    change HEq (B.pmap f (B.tr2 _ (B.zero2 x))) (B.tr2 _ (B.zero2 (B.map f x)))
    exact ((pmap_tr2_heq B f _ _).trans (B.zeroSnd_nat f x)).trans (tr2_heq B _ _).symm
  | succ n ih =>
    change HEq (B.pmap f (B.tr2 _ (B.add2 (B.nsmul2 u n) u)))
      (B.tr2 _ (B.add2 (B.nsmul2 (B.pmap f u) n) (B.pmap f u)))
    refine (pmap_tr2_heq B f _ _).trans ((B.addSnd_nat f _ _).trans ?_)
    exact (add2_heq_of_heq B (map_nsmul (B.map f) n y) (B.pmap f u) ih).trans
      (tr2_heq B _ _).symm

lemma totalFibreMap_totalFibreNsmulSnd {R S : LAlg R₀} (f : LHom R S) (N : ℕ) (t : B.Tot R) :
    B.Tmap f (B.totalFibreNsmulSnd N t) = B.totalFibreNsmulSnd N (B.Tmap f t) :=
  B.tot_ext rfl (map_nsmul (B.map f) N t.2.1) (pmap_nsmul2_heq B f t.2.2 N)

def Tsmul {R : LAlg R₀} (l : (R : Type u)ˣ) (t : B.Tot R) : B.Tot R :=
  ⟨t.1, t.2.1, B.smul l t.2.2⟩

lemma Tmap_Tsmul {R S : LAlg R₀} (f : LHom R S) (l : (R : Type u)ˣ) (t : B.Tot R) :
    B.Tmap f (B.Tsmul l t) =
      B.Tsmul (Units.map (f.1 : (R : Type u) →* (S : Type u)) l) (B.Tmap f t) :=
  B.tot_ext rfl rfl (heq_of_eq (B.pmap_smul f l t.2.2))

section Fibre

variable {F R₁ R₂ R : LAlg R₀} {p₁ : LHom F R₁} {p₂ : LHom F R₂} {f₁ : LHom R₁ R}
  {f₂ : LHom R₂ R}

lemma fibre_comm (hs : IsFibreSq p₁ p₂ f₁ f₂) : f₁.comp p₁ = f₂.comp p₂ := by
  apply Subtype.ext
  exact hs.1

lemma fibreG_unique (hs : IsFibreSq p₁ p₂ f₁ f₂) {a b : B.G F} (h1 : B.map p₁ a = B.map p₁ b)
    (h2 : B.map p₂ a = B.map p₂ b) : a = b := by
  have hc : B.map f₁ (B.map p₁ a) = B.map f₂ (B.map p₂ a) := by
    rw [← B.map_comp, ← B.map_comp, fibre_comm hs]
  exact (B.fibre_G p₁ p₂ f₁ f₂ hs _ _ hc).unique ⟨rfl, rfl⟩ ⟨h1.symm, h2.symm⟩

lemma exists_lift_of_isFibreSq (hs : IsFibreSq p₁ p₂ f₁ f₂) (a : B.Tot R₁) (b : B.Tot R₂)
    (h : B.Tmap f₁ a = B.Tmap f₂ b) : ∃ c : B.Tot F, B.Tmap p₁ c = a ∧ B.Tmap p₂ c = b := by
  obtain ⟨c, hc, -⟩ := B.fibre_P p₁ p₂ f₁ f₂ hs a b h
  exact ⟨c, hc.1, hc.2⟩

lemma ext_of_isFibreSq (hs : IsFibreSq p₁ p₂ f₁ f₂) {c c' : B.Tot F}
    (h1 : B.Tmap p₁ c = B.Tmap p₁ c') (h2 : B.Tmap p₂ c = B.Tmap p₂ c') : c = c' := by
  have e : B.Tmap f₁ (B.Tmap p₁ c) = B.Tmap f₂ (B.Tmap p₂ c) := by
    rw [← B.Tmap_comp, ← B.Tmap_comp, fibre_comm hs]
  exact (B.fibre_P p₁ p₂ f₁ f₂ hs _ _ e).unique ⟨rfl, rfl⟩ ⟨h1.symm, h2.symm⟩

end Fibre

theorem step1 {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R) (ξ : (R' : Type u))
    (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)
    (hB2 : HighestWeightVectorUniformBounds B) (N : ℕ) (hN : (N : (R' : Type u)) = 0) :
    ∃ O : ∀ V W : B.gg ⊗[R₀] π.ker, B.P R' (B.tg π (π.sqZero_of_span ξ hsurj hker hsq) V)
        (B.tg π (π.sqZero_of_span ξ hsurj hker hsq) W),
      (∀ V W, B.sw (O V W) = O W V) ∧
      ∀ (V W : B.gg ⊗[R₀] π.ker) (th : B.G R') (h : B.gg →ₗ[R₀] (R' : Type u))
        (hW : N • th = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) W),
        B.IsHeight Dp N (B.map π th) (π.1.toLinearMap ∘ₗ h) →
        ∀ u : B.P R' (B.tg π (π.sqZero_of_span ξ hsurj hker hsq) V) th,
        HEq (B.pmap π u) (B.zero1 (B.map π th)) →
        ∃ c : (R' : Type u)ˣ, (c : (R' : Type u)) = 1 - B.evK π h V ∧
          B.tr2 hW (B.nsmul2 u N) = B.smul c (O V W) := by
  have hπ : π.SqZero := π.sqZero_of_span ξ hsurj hker hsq
  have hNR : (N : (R : Type u)) = 0 := by rw [← map_natCast π.1, hN, map_zero]
  have hfs : IsFibreSq (FP.p₁ π Dp.π) (FP.p₂ π Dp.π) π Dp.π :=
    FP.isFibreSq π Dp.π (LHom.nilSurj_of_sqZero hπ) (LHom.nilSurj_of_sqZero Dp.sqZero)
  have hp₁ : (FP.p₁ π Dp.π).SqZero := p₁_sqZero π Dp
  have hfs2 : IsFibreSq (FP.p₁ (FP.p₁ π Dp.π) (FP.p₁ π Dp.π))
      (FP.p₂ (FP.p₁ π Dp.π) (FP.p₁ π Dp.π)) (FP.p₁ π Dp.π) (FP.p₁ π Dp.π) :=
    FP.isFibreSq _ _ (LHom.nilSurj_of_sqZero hp₁) (LHom.nilSurj_of_sqZero hp₁)
  have hsι := sm_comp_ι₁ π Dp hsurj hker hsq
  have hp₁ι := p₁_comp_ι₁ π Dp
  have hp₂ι := p₂_comp_ι₁ π Dp
  have hπs := π_comp_sm π Dp ξ hsurj hker hsq
  have hσ : ∀ y, B.map Dp.π (B.map Dp.σ y) = y := fun y => by
    rw [← B.map_comp, Dp.π_comp_σ, B.map_id]
  have htg0 : ∀ V, B.map π (B.tg π hπ V) = 0 := fun V => (B.tg_ker π hπ _).2 ⟨V, rfl⟩
  have htgD0 : ∀ Y, B.map Dp.π (B.tg Dp.π Dp.sqZero Y) = 0 :=
    fun Y => (B.tg_ker Dp.π Dp.sqZero _).2 ⟨Y, rfl⟩
  have htgp0 : ∀ Y, B.map (FP.p₁ π Dp.π) (B.tg (FP.p₁ π Dp.π) hp₁ Y) = 0 :=
    fun Y => (B.tg_ker (FP.p₁ π Dp.π) hp₁ _).2 ⟨Y, rfl⟩
  choose pre hpre using fun V =>
    LinearMap.lTensor_surjective B.gg (sm_ker_surj π Dp hsurj hker hsq) V
  have hx2 : ∀ V, B.map (FP.p₂ π Dp.π) (B.tg (FP.p₁ π Dp.π) hp₁ (pre V)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg
        ((FP.p₂ π Dp.π).1.toLinearMap.restrict (p₂_ker π Dp)) (pre V)) :=
    fun V => (B.tg_nat _ Dp.π hp₁ Dp.sqZero (FP.p₂ π Dp.π) (p₂_ker π Dp) (pre V)).symm
  have hx3 : ∀ V, B.map (sm π Dp ξ hsurj hker hsq) (B.tg (FP.p₁ π Dp.π) hp₁ (pre V)) =
      B.tg π hπ V := fun V => by
    rw [← B.tg_nat _ π hp₁ hπ (sm π Dp ξ hsurj hker hsq) (sm_ker π Dp hsurj hker hsq), hpre]
  have hy1 : ∀ W, B.map (FP.p₁ π Dp.π) (B.map (ι₁ π Dp) (B.tg π hπ W)) = B.tg π hπ W :=
    fun W => by rw [← B.map_comp, hp₁ι, B.map_id]
  have hy2 : ∀ W, B.map (FP.p₂ π Dp.π) (B.map (ι₁ π Dp) (B.tg π hπ W)) = 0 :=
    fun W => by rw [← B.map_comp, hp₂ι, B.map_comp, htg0, map_zero]
  have hy3 : ∀ W, B.map (sm π Dp ξ hsurj hker hsq) (B.map (ι₁ π Dp) (B.tg π hπ W)) =
      B.tg π hπ W := fun W => by rw [← B.map_comp, hsι, B.map_id]

  have hcompat : ∀ V W, B.Tmap π (⟨0, B.tg π hπ W, B.zero1 (B.tg π hπ W)⟩ : B.Tot R') =
      B.Tmap Dp.π ⟨B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg
        ((FP.p₂ π Dp.π).1.toLinearMap.restrict (p₂_ker π Dp)) (pre V)), 0,
        B.zero2 (B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg
        ((FP.p₂ π Dp.π).1.toLinearMap.restrict (p₂_ker π Dp)) (pre V)))⟩ := fun V W =>
    B.tot_ext (by show B.map π 0 = B.map Dp.π _; rw [map_zero, htgD0])
      (by show B.map π _ = B.map Dp.π 0; rw [map_zero, htg0])
      (by
        show HEq (B.pmap π (B.zero1 _)) (B.pmap Dp.π (B.zero2 _))
        refine (B.zeroFst_nat π _).trans ?_
        refine (B.heq_zero1 (htg0 W)).trans ?_
        rw [B.zeroFst_zero]
        exact (B.heq_zero2 (htgD0 _).symm).trans (B.zeroSnd_nat Dp.π _).symm)
  choose oD hoD using fun V W => B.exists_lift_of_isFibreSq hfs _ _ (hcompat V W)
  have hoD1 : ∀ V W, (oD V W).1 = B.tg (FP.p₁ π Dp.π) hp₁ (pre V) := fun V W =>
    B.fibreG_unique hfs (((B.tot_eq (hoD V W).1).1).trans (htgp0 _).symm)
      (((B.tot_eq (hoD V W).2).1).trans (hx2 V).symm)
  have hoD2 : ∀ V W, (oD V W).2.1 = B.map (ι₁ π Dp) (B.tg π hπ W) := fun V W =>
    B.fibreG_unique hfs (((B.tot_eq (hoD V W).1).2.1).trans (hy1 W).symm)
      (((B.tot_eq (hoD V W).2).2.1).trans (hy2 W).symm)
  have hOi1 : ∀ V W, B.map (sm π Dp ξ hsurj hker hsq) (oD V W).1 = B.tg π hπ V :=
    fun V W => by rw [hoD1, hx3]
  have hOi2 : ∀ V W, B.map (sm π Dp ξ hsurj hker hsq) (oD V W).2.1 = B.tg π hπ W :=
    fun V W => by rw [hoD2, hy3]
  choose O hO using fun V W =>
    B.exists_cast (hOi1 V W) (hOi2 V W) (B.pmap (sm π Dp ξ hsurj hker hsq) (oD V W).2.2)
  refine ⟨O, ?_, ?_⟩
  ·
    intro V W
    have hc2 : B.Tmap (FP.p₁ π Dp.π) (⟨B.tg (FP.p₁ π Dp.π) hp₁ (pre W), 0,
        B.zero2 (B.tg (FP.p₁ π Dp.π) hp₁ (pre W))⟩ : B.Tot (FP π Dp.π)) =
        B.Tmap (FP.p₁ π Dp.π) ⟨0, B.tg (FP.p₁ π Dp.π) hp₁ (pre V),
          B.zero1 (B.tg (FP.p₁ π Dp.π) hp₁ (pre V))⟩ :=
      B.tot_ext (by show B.map _ _ = B.map _ 0; rw [htgp0, map_zero])
        (by show B.map _ 0 = B.map _ _; rw [htgp0, map_zero])
        (by
          show HEq (B.pmap _ (B.zero2 _)) (B.pmap _ (B.zero1 _))
          refine (B.zeroSnd_nat _ _).trans ?_
          refine (B.heq_zero2 (htgp0 _)).trans ?_
          rw [← B.zeroFst_zero]
          exact (B.heq_zero1 (htgp0 _).symm).trans (B.zeroFst_nat _ _).symm)
    obtain ⟨o2, ho2a, ho2b⟩ := B.exists_lift_of_isFibreSq hfs2 _ _ hc2
    have hφ : ∀ t : (FP (FP.p₁ π Dp.π) (FP.p₁ π Dp.π) : Type u),
        π.1 (((sm π Dp ξ hsurj hker hsq).comp (FP.p₂ (FP.p₁ π Dp.π) (FP.p₁ π Dp.π))).1 t) =
        Dp.π.1 (((FP.p₂ π Dp.π).comp (FP.p₁ (FP.p₁ π Dp.π) (FP.p₁ π Dp.π))).1 t) := fun t => by
      have e1 := congrArg (fun φ : LHom (FP π Dp.π) R => φ.1 t.1.2) hπs
      have e2 : t.1.1.1.1 = t.1.2.1.1 := FP.mem (FP.p₁ π Dp.π) (FP.p₁ π Dp.π) t
      show π.1 ((sm π Dp ξ hsurj hker hsq).1 t.1.2) = Dp.π.1 t.1.1.1.2
      refine e1.trans ?_
      show π.1 t.1.2.1.1 = _
      rw [← e2]; exact FP.mem π Dp.π t.1.1
    have hψ : ∀ t : (FP (FP.p₁ π Dp.π) (FP.p₁ π Dp.π) : Type u),
        π.1 (((sm π Dp ξ hsurj hker hsq).comp (FP.p₁ (FP.p₁ π Dp.π) (FP.p₁ π Dp.π))).1 t) =
        Dp.π.1 (((FP.p₂ π Dp.π).comp (FP.p₂ (FP.p₁ π Dp.π) (FP.p₁ π Dp.π))).1 t) := fun t => by
      have e1 := congrArg (fun φ : LHom (FP π Dp.π) R => φ.1 t.1.1) hπs
      have e2 : t.1.1.1.1 = t.1.2.1.1 := FP.mem (FP.p₁ π Dp.π) (FP.p₁ π Dp.π) t
      show π.1 ((sm π Dp ξ hsurj hker hsq).1 t.1.1) = Dp.π.1 t.1.2.1.2
      refine e1.trans ?_
      show π.1 t.1.1.1.1 = _
      rw [e2]; exact FP.mem π Dp.π t.1.2
    let φ := FP.lift π Dp.π _ _ hφ
    let ψ := FP.lift π Dp.π _ _ hψ
    have hsφψ : (sm π Dp ξ hsurj hker hsq).comp φ = (sm π Dp ξ hsurj hker hsq).comp ψ :=
      LHom.ext' fun t => by
        show (t.1.2.1.1 + ell π ξ hsurj (Dp.κ t.1.2.1.2)) + ell π ξ hsurj (Dp.κ t.1.1.1.2) =
          (t.1.1.1.1 + ell π ξ hsurj (Dp.κ t.1.1.1.2)) + ell π ξ hsurj (Dp.κ t.1.2.1.2)
        rw [show t.1.1.1.1 = t.1.2.1.1 from FP.mem (FP.p₁ π Dp.π) (FP.p₁ π Dp.π) t]; ring
    have hφo : B.Tmap φ o2 = oD W V := B.ext_of_isFibreSq hfs
      (by
        rw [← B.Tmap_comp, (hoD W V).1,
          show (FP.p₁ π Dp.π).comp φ = (sm π Dp ξ hsurj hker hsq).comp
            (FP.p₂ (FP.p₁ π Dp.π) (FP.p₁ π Dp.π)) from LHom.ext' fun _ => rfl,
          B.Tmap_comp, ho2b]
        exact B.tot_ext (map_zero _) (hx3 V) ((B.zeroFst_nat _ _).trans (B.heq_zero1 (hx3 V))))
      (by
        rw [← B.Tmap_comp, (hoD W V).2,
          show (FP.p₂ π Dp.π).comp φ = (FP.p₂ π Dp.π).comp
            (FP.p₁ (FP.p₁ π Dp.π) (FP.p₁ π Dp.π)) from LHom.ext' fun _ => rfl,
          B.Tmap_comp, ho2a]
        exact B.tot_ext (hx2 W) (map_zero _) ((B.zeroSnd_nat _ _).trans (B.heq_zero2 (hx2 W))))
    have hψo : B.Tmap ψ o2 = B.Tsw (oD V W) := B.ext_of_isFibreSq hfs
      (by
        rw [← B.Tmap_comp, B.Tmap_Tsw, (hoD V W).1,
          show (FP.p₁ π Dp.π).comp ψ = (sm π Dp ξ hsurj hker hsq).comp
            (FP.p₁ (FP.p₁ π Dp.π) (FP.p₁ π Dp.π)) from LHom.ext' fun _ => rfl,
          B.Tmap_comp, ho2a]
        exact B.tot_ext (hx3 W) (map_zero _) ((B.zeroSnd_nat _ _).trans
          ((B.heq_zero2 (hx3 W)).trans (heq_of_eq (B.sw_zero1 _).symm))))
      (by
        rw [← B.Tmap_comp, B.Tmap_Tsw, (hoD V W).2,
          show (FP.p₂ π Dp.π).comp ψ = (FP.p₂ π Dp.π).comp
            (FP.p₂ (FP.p₁ π Dp.π) (FP.p₁ π Dp.π)) from LHom.ext' fun _ => rfl,
          B.Tmap_comp, ho2b]
        exact B.tot_ext (map_zero _) (hx2 V) ((B.zeroFst_nat _ _).trans
          ((B.heq_zero1 (hx2 V)).trans (heq_of_eq (B.sw_zero2 _).symm))))
    have key : B.Tmap (sm π Dp ξ hsurj hker hsq) (oD W V) =
        B.Tsw (B.Tmap (sm π Dp ξ hsurj hker hsq) (oD V W)) := by
      rw [← hφo, ← B.Tmap_comp, hsφψ, B.Tmap_comp, hψo, B.Tmap_Tsw]
    obtain ⟨-, -, k3⟩ := B.tot_eq key
    apply eq_of_heq
    refine (B.sw_hcongr (hOi1 V W).symm (hOi2 V W).symm (hO V W)).trans ?_
    exact k3.symm.trans (hO W V).symm
  ·
    intro V W th h hW hh u hu
    obtain ⟨-, ⟨-, hNX, -⟩, -⟩ := hh 0
    obtain ⟨u₀, hu₀⟩ := B.exists_lift_red Dp (htgD0 (LinearMap.lTensor B.gg
        ((FP.p₂ π Dp.π).1.toLinearMap.restrict (p₂_ker π Dp)) (pre V))) (hσ (B.map π th))
      (B.zero1 (B.map π th))
    obtain ⟨-, cD, hcD, hN2⟩ :=
      B.ht_gen Dp hB2 N hNR (B.map π th) (π.1.toLinearMap ∘ₗ h) hh _ u₀ hu₀
    have hc3 : B.Tmap π (⟨0, th, B.zero1 th⟩ : B.Tot R') =
        B.Tmap Dp.π ⟨B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg
          ((FP.p₂ π Dp.π).1.toLinearMap.restrict (p₂_ker π Dp)) (pre V)),
          B.map Dp.σ (B.map π th), u₀⟩ :=
      B.tot_ext (by show B.map π 0 = B.map Dp.π _; rw [map_zero, htgD0])
        (hσ (B.map π th)).symm ((B.zeroFst_nat π th).trans hu₀.symm)
    obtain ⟨uD, huDa, huDb⟩ := B.exists_lift_of_isFibreSq hfs _ _ hc3
    have huD1 : uD.1 = B.tg (FP.p₁ π Dp.π) hp₁ (pre V) := B.fibreG_unique hfs
      (((B.tot_eq huDa).1).trans (htgp0 _).symm) (((B.tot_eq huDb).1).trans (hx2 V).symm)
    have huD2 : uD.2.1 = B.map (ι₁ π Dp) th := B.fibreG_unique hfs
      (((B.tot_eq huDa).2.1).trans (by rw [← B.map_comp (ι₁ π Dp) (FP.p₁ π Dp.π), hp₁ι, B.map_id]))
      (((B.tot_eq huDb).2.1).trans (by rw [← B.map_comp (ι₁ π Dp) (FP.p₂ π Dp.π), hp₂ι, B.map_comp]))
    have hi1 : B.map (sm π Dp ξ hsurj hker hsq) uD.1 = B.tg π hπ V := by rw [huD1, hx3]
    have hi2 : B.map (sm π Dp ξ hsurj hker hsq) uD.2.1 = th := by
      rw [huD2, ← B.map_comp, hsι, B.map_id]
    obtain ⟨w', hw'⟩ := B.exists_cast hi1 hi2 (B.pmap (sm π Dp ξ hsurj hker hsq) uD.2.2)
    have hw'red : HEq (B.pmap π w') (B.zero1 (B.map π th)) := by
      refine (B.pmap_hcongr π hi1.symm hi2.symm hw').trans ?_
      refine (B.pmap_comp _ π _).symm.trans ?_
      refine (B.pmap_congr_hom hπs _).trans ?_
      refine (B.pmap_comp _ π _).trans ?_
      obtain ⟨e1, e2, e3⟩ := B.tot_eq huDa
      refine (B.pmap_hcongr π e1 e2 e3).trans ?_
      exact B.zeroFst_nat π th
    obtain ⟨μ, rfl⟩ := B.exists_smul w' u
    have hμ : Units.map (π.1 : (R' : Type u) →* (R : Type u)) μ = 1 := by
      apply B.smul_eq_self (u := B.pmap π w')
      rw [← B.pmap_smul]
      exact eq_of_heq (hu.trans hw'red.symm)
    have hμN : μ ^ N = 1 :=
      LHom.pow_eq_one hπ hN μ (by have := congrArg Units.val hμ; simpa using this)
    obtain ⟨e, hedef⟩ : ∃ e, e = evalT ((ι₁ π Dp).1.toLinearMap ∘ₗ h) (FP.p₁ π Dp.π).ker (pre V) :=
      ⟨_, rfl⟩
    have he1 : (FP.p₁ π Dp.π).1 e = 0 := by
      rw [hedef]; exact (RingHom.mem_ker).1 (evalT_mem _ _ _)
    have hee : e * e = 0 := LHom.mul_eq_zero hp₁ he1 he1
    have hl1 : Units.map ((FP.p₁ π Dp.π).1 : (FP π Dp.π : Type u) →* (R' : Type u))
        (unitSub e hee) = 1 := Units.ext (by
      show (FP.p₁ π Dp.π).1 (1 - e) = 1; rw [map_sub, map_one, he1, sub_zero])
    have hp₂e : (FP.p₂ π Dp.π).1 e = evalT (Dp.σ.1.toLinearMap ∘ₗ (π.1.toLinearMap ∘ₗ h))
        Dp.π.ker (LinearMap.lTensor B.gg
          ((FP.p₂ π Dp.π).1.toLinearMap.restrict (p₂_ker π Dp)) (pre V)) := by
      rw [hedef, evalT_nat (FP.p₂ π Dp.π).1 _ _ _ (p₂_ker π Dp)]; rfl
    have hl2 : Units.map ((FP.p₂ π Dp.π).1 : (FP π Dp.π : Type u) →* (Dp.D : Type u))
        (unitSub e hee) = cD := Units.ext (by
      show (FP.p₂ π Dp.π).1 (1 - e) = (cD : (Dp.D : Type u)); rw [map_sub, map_one, hp₂e, hcD])
    have hse : (sm π Dp ξ hsurj hker hsq).1 e = B.evK π h V := by
      rw [hedef, evalT_nat (sm π Dp ξ hsurj hker hsq).1 _ _ _ (sm_ker π Dp hsurj hker hsq), hpre]
      show evalT _ π.ker V = evalT h π.ker V
      congr 1
      ext g
      exact congrArg (fun φ : LHom R' R' => φ.1 (h g)) hsι
    refine ⟨Units.map ((sm π Dp ξ hsurj hker hsq).1 : (FP π Dp.π : Type u) →* (R' : Type u))
      (unitSub e hee), by
      show (sm π Dp ξ hsurj hker hsq).1 (1 - e) = 1 - B.evK π h V; rw [map_sub, map_one, hse], ?_⟩
    have hkey : B.totalFibreNsmulSnd N uD = B.Tsmul (unitSub e hee) (oD V W) := B.ext_of_isFibreSq hfs
      (by
        rw [B.totalFibreMap_totalFibreNsmulSnd, huDa, B.Tmap_Tsmul, hl1, (hoD V W).1]
        exact B.tot_ext rfl hW ((B.nsmul2_zero1 th N).trans
          ((B.heq_zero1 hW).trans (heq_of_eq (B.one_smul _).symm))))
      (by
        rw [B.totalFibreMap_totalFibreNsmulSnd, huDb, B.Tmap_Tsmul, hl2, (hoD V W).2]
        exact B.tot_ext rfl hNX hN2)
    have k := congrArg (B.Tmap (sm π Dp ξ hsurj hker hsq)) hkey
    rw [B.totalFibreMap_totalFibreNsmulSnd, B.Tmap_Tsmul] at k
    obtain ⟨-, -, k3⟩ := B.tot_eq k
    apply eq_of_heq
    refine (B.castSnd_heq hW _).trans ?_
    rw [B.nsmul2_smul, hμN, B.one_smul]
    refine (B.nsmul2_hcongr hi1.symm hi2.symm N hw').trans ?_
    refine k3.trans ?_
    exact B.smul_hcongr (hOi1 V W) (hOi2 V W) _ (hO V W).symm

end BX

end ReciprocityTheory.PGsh
