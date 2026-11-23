import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationTorsionTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

open scoped TensorProduct
open GlobalTheory GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Closed

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup

def isoOfBijective {p : ℕ} {O : Type} [CommRing O] {G H : PDivGroup p O} (f : G ⟶ H)
    (hf : ∀ n, Function.Bijective (f.app n)) : G ≅ H where
  hom := f
  inv := ⟨fun n => ((BialgEquiv.ofBijective (f.app n) (hf n)).symm : G.A n →ₐc[O] H.A n),
    fun n => BialgHom.ext fun a => by
      obtain ⟨b, rfl⟩ := (hf (n + 1)).2 a
      have e1 : (BialgEquiv.ofBijective (f.app (n + 1)) (hf (n + 1))).symm (f.app (n + 1) b) = b :=
        (BialgEquiv.ofBijective (f.app (n + 1)) (hf (n + 1))).symm_apply_apply b
      change H.res n ((BialgEquiv.ofBijective (f.app (n + 1)) (hf (n + 1))).symm (f.app (n + 1) b)) =
        (BialgEquiv.ofBijective (f.app n) (hf n)).symm (G.res n (f.app (n + 1) b))
      rw [e1, res_app]
      exact ((BialgEquiv.ofBijective (f.app n) (hf n)).symm_apply_apply _).symm⟩
  hom_inv_id := hom_ext fun n => BialgHom.ext fun a =>
    (BialgEquiv.ofBijective (f.app n) (hf n)).apply_symm_apply a
  inv_hom_id := hom_ext fun n => BialgHom.ext fun a =>
    (BialgEquiv.ofBijective (f.app n) (hf n)).symm_apply_apply a

@[simp] theorem isoOfBijective_hom {p : ℕ} {O : Type} [CommRing O] {G H : PDivGroup p O} (f : G ⟶ H)
    (hf : ∀ n, Function.Bijective (f.app n)) : (isoOfBijective f hf).hom = f := rfl

end GlobalTheory.PDivGroup

namespace GlobalTheory.GroupBplus.Closed

theorem exists_tensor_of_pts {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {A : Type} [CommRing A]
    [HopfAlgebra k A] [Module.Finite k A] (F : (A →ₐ[k] k) → (A →ₐ[k] k) → k) :
    ∃ u : A ⊗[k] A, ∀ y x, WeilPhi.ev y x u = F y x := by
  classical
  have hc := TateFree.natCard_pts k k (A ⊗[k] A)
  have hB : Module.finrank k (k ⊗[k] (A ⊗[k] A)) = Module.finrank k (A ⊗[k] A) :=
    (Algebra.TensorProduct.lid k (A ⊗[k] A)).toLinearEquiv.finrank_eq
  haveI : Nontrivial (A ⊗[k] A) := (Bialgebra.counitAlgHom k (A ⊗[k] A)).toRingHom.domain_nontrivial
  haveI : Finite (A ⊗[k] A →ₐ[k] k) :=
    Nat.finite_of_card_ne_zero (by rw [hc, hB]; exact Module.finrank_pos.ne')
  letI := Fintype.ofFinite (A ⊗[k] A →ₐ[k] k)
  let E : A ⊗[k] A →ₗ[k] ((A ⊗[k] A →ₐ[k] k) → k) :=
    { toFun := fun b ψ => ψ b
      map_add' := fun a b => funext fun ψ => map_add ψ a b
      map_smul' := fun c b => funext fun ψ => by simp }
  have hinj : Function.Injective E := fun a b h =>
    TateFree.eq_of_forall_pts k k (A ⊗[k] A) fun ψ => congrFun h ψ
  have hsurj : Function.Surjective E :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hc, hB])).1 hinj
  obtain ⟨u, hu⟩ := hsurj fun ψ =>
    F (ψ.comp Algebra.TensorProduct.includeLeft) (ψ.comp Algebra.TensorProduct.includeRight)
  refine ⟨u, fun y x => ?_⟩
  have h := congrFun hu (WeilPhi.ev y x)
  simp only [E, LinearMap.coe_mk, AddHom.coe_mk, WeilPhi.ev_comp_left, WeilPhi.ev_comp_right] at h
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k]
  {Dw : Datum H} {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k}
  (tw : GG.TorsionTower t.G) (I : GeomTate Dw t)

omit [Fact p.Prime] in

theorem ev_nsmul (m j : ℕ) (a : Dw.La) : I.ev m (j • a) = I.ev m a ^ j := by
  induction j with
  | zero =>
    have h := I.add m 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_right.1 h.symm
  | succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem latPt_surj (n : ℕ) (y : GG.A n →ₐ[k] k) : ∃ a, latPt tw I n a = y := by
  have hp := pow_pos (Fact.out : p.Prime).pos n
  have hz : (spOver y ≫ tw.y n) ^ p ^ n = 1 := (tw.exists_iff n _).1 ⟨y, rfl⟩
  obtain ⟨a, ha⟩ := (I.onto (p ^ n) hp (selfIso.inv ≫ spOver y ≫ tw.y n)).1
    (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
  exact ⟨a, tw.inj n k _ _ (by rw [latPt_y, ha, Iso.hom_inv_id_assoc])⟩

theorem latPt_pow_smul (n : ℕ) (d : Dw.La) : toConv (latPt tw I n (p ^ n • d)) = 1 := by
  have hp := pow_pos (Fact.out : p.Prime).pos n
  refine TorsionTower.pts_injective tw n k ?_
  rw [map_one, TorsionTower.pts_apply, WithConv.ofConv_toConv, latPt_y,
    (I.ker (p ^ n) hp _).2 ⟨d, rfl⟩, MonObj.comp_one]

theorem exists_of_latPt_eq (n : ℕ) {a a' : Dw.La} (h : latPt tw I n a = latPt tw I n a') :
    ∃ c, a = a' + p ^ n • c := by
  have hp := pow_pos (Fact.out : p.Prime).pos n
  have h1 : toConv (latPt tw I n (a - a')) = 1 := by
    have := latPt_add tw I n (a - a') a'
    rw [sub_add_cancel, h] at this
    exact mul_eq_right.1 this.symm
  have h2 : I.ev (p ^ n) (a - a') = 1 := by
    have h3 := congrArg (TorsionTower.pts tw n k) h1
    rw [map_one, TorsionTower.pts_apply, WithConv.ofConv_toConv, latPt_y] at h3
    have h4 := congrArg (selfIso.inv ≫ ·) h3
    simpa only [Iso.inv_hom_id_assoc, MonObj.comp_one] using h4
  obtain ⟨c, hc⟩ := (I.ker (p ^ n) hp _).1 h2
  exact ⟨c, by rw [← hc]; abel⟩

theorem latPt_res (n : ℕ) (b : Dw.La) :
    (latPt tw I n b).comp (GG.res n : GG.A (n + 1) →ₐ[k] GG.A n) = latPt tw I (n + 1) (p • b) := by
  refine tw.inj (n + 1) k _ _ ?_
  rw [← spOver_comp, Category.assoc, tw.res, latPt_y, latPt_y, ev_nsmul, pow_succ,
    I.tower (p ^ n) p (pow_pos (Fact.out : p.Prime).pos n) (Fact.out : p.Prime).pos]

omit [Fact p.Prime] in

theorem zeta_zpow_add (hp : 0 < p) (n : ℕ) (x y : ℤ) :
    I.ζ (p ^ n) ^ (x + p ^ n • y) = I.ζ (p ^ n) ^ x := by
  rw [zpow_add, nsmul_eq_mul, zpow_mul, zpow_natCast, (I.ζ_prim (p ^ n) (pow_pos hp n)).pow_eq_one,
    one_zpow, _root_.mul_one]

theorem latPt_eq_of_forall (n : ℕ) {b b' : Dw.La}
    (h : ∀ a, I.ζ (p ^ n) ^ Dw.EF a b = I.ζ (p ^ n) ^ Dw.EF a b') : latPt tw I n b = latPt tw I n b' := by
  have hp := pow_pos (Fact.out : p.Prime).pos n
  have hdvd : ∀ a, ((p ^ n : ℕ) : ℤ) ∣ Dw.EF (b - b') a := fun a => by
    have h1 := h a
    have e : Dw.EF a b = Dw.EF a b' + Dw.EF a (b - b') := by rw [map_sub]; abel
    rw [e, zpow_add, mul_eq_left] at h1
    have h2 := ((I.ζ_prim (p ^ n) hp).zpow_eq_one_iff_dvd _).1 h1
    have skew : Dw.EF (b - b') a = - Dw.EF a (b - b') := by
      have := Dw.alt (a + (b - b'))
      simp only [map_add, LinearMap.add_apply, Dw.alt] at this
      linarith
    rw [skew]
    exact dvd_neg.2 h2
  let lf : Dw.La →ₗ[ℤ] ℤ :=
    { toFun := fun a => Dw.EF (b - b') a / ((p ^ n : ℕ) : ℤ)
      map_add' := fun x y => by rw [map_add, Int.add_ediv_of_dvd_left (hdvd x)]
      map_smul' := fun m x => by
        rw [map_zsmul, RingHom.id_apply, smul_eq_mul, smul_eq_mul]
        exact Int.mul_ediv_assoc m (hdvd x) }
  obtain ⟨d, hd⟩ := Dw.unimod.2 lf
  have hcd : b - b' = p ^ n • d := Dw.unimod.1 (LinearMap.ext fun a => by
    rw [map_nsmul, LinearMap.smul_apply, hd]
    change Dw.EF (b - b') a = p ^ n • (Dw.EF (b - b') a / ((p ^ n : ℕ) : ℤ))
    rw [nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd a)).symm)
  have hb : b = b' + p ^ n • d := by rw [← hcd]; abel
  have := latPt_add tw I n b' (p ^ n • d)
  rw [latPt_pow_smul, _root_.mul_one, ← hb] at this
  exact congrArg ofConv this

end GlobalTheory.GroupBplus.Closed

namespace GlobalTheory.GroupBplus.Closed

theorem exists_pol_pairing {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k}
    (tw : GG.TorsionTower t.G) (I : GeomTate Dw t) : ∃ pol : GG ≅ GG.dual,
      (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k pol.hom (tau tw I y))) n =
        ((I.ζ (p ^ n) ^ Dw.EF x y : kˣ) : k)) := by
  classical
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  have vl : ∀ n a a' c b, a = a' + p ^ n • c →
      I.ζ (p ^ n) ^ Dw.EF a b = I.ζ (p ^ n) ^ Dw.EF a' b := fun n a a' c b h => by
    rw [h, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, zeta_zpow_add I hpp]
  have vr : ∀ n a b b' c, b = b' + p ^ n • c →
      I.ζ (p ^ n) ^ Dw.EF a b = I.ζ (p ^ n) ^ Dw.EF a b' := fun n a b b' c h => by
    rw [h, map_add, map_nsmul, zeta_zpow_add I hpp]
  choose rep hrep using latPt_surj tw I
  have hval : ∀ n a b, I.ζ (p ^ n) ^ Dw.EF (rep n (latPt tw I n a)) (rep n (latPt tw I n b)) =
      I.ζ (p ^ n) ^ Dw.EF a b := fun n a b => by
    obtain ⟨c, hc⟩ := exists_of_latPt_eq tw I n (hrep n (latPt tw I n a))
    obtain ⟨c', hc'⟩ := exists_of_latPt_eq tw I n (hrep n (latPt tw I n b))
    rw [vl n _ _ c _ hc, vr n _ _ _ c' hc']
  choose u hu using fun n => exists_tensor_of_pts (A := GG.A n)
    (fun y x => ((I.ζ (p ^ n) ^ Dw.EF (rep n y) (rep n x) : kˣ) : k))
  have hf : ∀ n a b, WeilPhi.ev (latPt tw I n a) (latPt tw I n b) (u n) =
      ((I.ζ (p ^ n) ^ Dw.EF a b : kˣ) : k) := fun n a b => by rw [hu, hval]
  have h1 : ∀ n, (1 : WithConv (GG.A n →ₐ[k] k)).ofConv = latPt tw I n 0 := fun n => by
    have := latPt_pow_smul tw I n 0
    rw [smul_zero] at this
    rw [← this]
  have hmul : ∀ n (y y' : WithConv (GG.A n →ₐ[k] k)) a a', latPt tw I n a = y.ofConv →
      latPt tw I n a' = y'.ofConv → (y * y').ofConv = latPt tw I n (a + a') := fun n y y' a a' ha ha' => by
    have e : toConv (latPt tw I n (a + a')) = y * y' := by rw [latPt_add, ha, ha']
    rw [← e]
  have hB : ∀ n, WeilPhi.IsBimul (u n) := fun n =>
    { one_left := fun x => by
        obtain ⟨b, rfl⟩ := latPt_surj tw I n x
        rw [h1, hf]; simp
      one_right := fun x => by
        obtain ⟨b, rfl⟩ := latPt_surj tw I n x
        rw [h1, hf]; simp
      mul_left := fun y y' x => by
        obtain ⟨a, ha⟩ := latPt_surj tw I n y.ofConv
        obtain ⟨a', ha'⟩ := latPt_surj tw I n y'.ofConv
        obtain ⟨b, rfl⟩ := latPt_surj tw I n x
        rw [hmul n y y' a a' ha ha', ← ha, ← ha', hf, hf, hf, map_add, LinearMap.add_apply, zpow_add,
          Units.val_mul]
      mul_right := fun y y' x => by
        obtain ⟨a, ha⟩ := latPt_surj tw I n y.ofConv
        obtain ⟨a', ha'⟩ := latPt_surj tw I n y'.ofConv
        obtain ⟨b, rfl⟩ := latPt_surj tw I n x
        rw [hmul n y y' a a' ha ha', ← ha, ← ha', hf, hf, hf, map_add, zpow_add, Units.val_mul] }
  have hl : ∀ (n : ℕ) (y : GG.A (n + 1) →ₐ[k] k) (x : GG.A n →ₐ[k] k),
      WeilPhi.ev y (x.comp (GG.res n : GG.A (n + 1) →ₐ[k] GG.A n)) (u (n + 1)) =
        WeilPhi.ev (y.comp (GG.mulP n : GG.A n →ₐ[k] GG.A (n + 1))) x (u n) := fun n y x => by
    obtain ⟨a, rfl⟩ := latPt_surj tw I (n + 1) y
    obtain ⟨b, rfl⟩ := latPt_surj tw I n x
    rw [latPt_res, latPt_compat, hf, hf, map_nsmul, nsmul_eq_mul, zpow_mul, zpow_natCast, pow_succ,
      I.ζ_pow (p ^ n) p (pow_pos hpp n) hpp]
  obtain ⟨φ, hφ⟩ := WeilPhi.exists_hom_dual k GG u hB hl
  have hbij : ∀ n, Function.Bijective (φ.app n) := fun n => by
    let P : (GG.A n →ₐ[k] k) → (GG.dual.A n →ₐ[k] k) := fun x =>
      x.comp (φ.app n : GG.dual.A n →ₐ[k] GG.A n)
    have hPi : Function.Injective P := fun x x' hxx => by
      obtain ⟨s', rfl⟩ := GG.pt_surjective k n x
      obtain ⟨s'', rfl⟩ := GG.pt_surjective k n x'
      dsimp only at hxx ⊢
      obtain ⟨b, hb⟩ := latPt_surj tw I n (s'.pt n)
      obtain ⟨b', hb'⟩ := latPt_surj tw I n (s''.pt n)
      have e : (tateMap GG GG.dual k φ s').pt n = (tateMap GG GG.dual k φ s'').pt n :=
        AlgHom.ext fun a => DFunLike.congr_fun hxx a
      have e2 : charElem (tateMap GG GG.dual k φ s') n = charElem (tateMap GG GG.dual k φ s'') n := by
        simp only [charElem, TateOver.conv, e]
      rw [← hb, ← hb']
      refine latPt_eq_of_forall tw I n fun a => Units.ext ?_
      have h2 := hφ (tau tw I a) s' n
      have h3 := hφ (tau tw I a) s'' n
      rw [muRoot_pairing] at h2 h3
      rw [e2, h3, tau_pt, ← hb, ← hb', hf, hf] at h2
      exact h2.symm
    have hcard : Nat.card (GG.A n →ₐ[k] k) = Nat.card (GG.dual.A n →ₐ[k] k) := by
      rw [GG.natCard_pts_eq k n, GG.dual.natCard_pts_eq k n]
    haveI : Finite (GG.dual.A n →ₐ[k] k) :=
      Nat.finite_of_card_ne_zero (by rw [GG.dual.natCard_pts_eq k n]; positivity)
    have hPs : Function.Surjective P := (hPi.bijective_of_nat_card_le hcard.ge).2
    have hinj : Function.Injective (φ.app n) := fun b b' hbb =>
      TateFree.eq_of_forall_pts k k (GG.dual.A n) fun z => by
        obtain ⟨x, rfl⟩ := hPs z
        exact congrArg x hbb
    have hfr : Module.finrank k (GG.dual.A n) = Module.finrank k (GG.A n) := by
      have e1 := TateFree.natCard_pts k k (GG.dual.A n)
      have e2 := TateFree.natCard_pts k k (GG.A n)
      rw [(Algebra.TensorProduct.lid k _).toLinearEquiv.finrank_eq] at e1 e2
      rw [← e1, ← e2, hcard]
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
      (f := (φ.app n).toLinearMap)).1 hinj⟩
  refine ⟨isoOfBijective φ hbij, fun x y n => ?_⟩
  rw [isoOfBijective_hom, hφ, tau_pt, tau_pt, hf]

end GlobalTheory.GroupBplus.Closed
