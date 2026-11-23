import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory

namespace GlobalTheory

namespace PDiv

variable {p : ℕ} [hp : Fact p.Prime] {R A : Type} [CommRing R] [CommRing A]

theorem exists_dualSystem (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ s : Finset (CartierDual R M × M), ∀ a, ∑ i ∈ s, i.1 a • i.2 = a := by
  obtain ⟨u, hu⟩ := (dualTensorHom_bijective (R := R) (M := M) (N := M)).2 LinearMap.id
  obtain ⟨u, rfl⟩ := (LinearEquiv.rTensor M (CartierDual.toDual R M)).surjective u
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset u
  exact ⟨s, fun a => by simpa using LinearMap.congr_fun hu a⟩

variable [Bialgebra R A]

theorem dUnit_pow_prime (h : (p : R) = 0) (a : A) : dUnit R (a ^ p) = 0 := by
  have key : ∀ k : ℕ, dUnit R (a ^ (k + 1)) =
      ((k + 1 : ℕ) * counitAlgHom R A a ^ k : R) • dUnit R a := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, dUnit, AugCot.d_mul, ← dUnit, ← dUnit, ih, smul_smul, ← add_smul, map_pow]
      congr 1
      push_cast
      ring
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
  have := key k
  rwa [← Nat.succ_eq_add_one, ← hk, h, zero_mul, zero_smul] at this

variable [IsCocomm R A]

theorem convPow_prime_apply (h : (p : R) = 0) {B ι : Type} [CommRing B] [Algebra R B] (s : Finset ι)
    (φ : ι → CartierDual R A) (b : ι → B) (f : A →ₗ[R] B) (hf : ∀ a, f a = ∑ i ∈ s, φ i a • b i)
    (a : A) : (toConv f ^ p) a = ∑ i ∈ s, (φ i ^ p) a • b i ^ p := by
  let j : CartierDual R A →* WithConv (A →ₗ[R] B) :=
    { toFun := fun χ => toConv ((Algebra.ofId R B).toLinearMap ∘ₗ χ.ofConv)
      map_one' := rfl
      map_mul' := fun χ ψ => congrArg toConv (LinearMap.algHom_comp_convMul_distrib _ χ ψ) }
  have hj : ∀ (c : B) χ a, (c • j χ).ofConv a = χ a • c := fun c χ a =>
    (mul_comm _ _).trans (Algebra.smul_def _ _).symm
  have e : toConv f = ∑ i ∈ s, b i • j (φ i) := WithConv.ext (LinearMap.ext fun a => by
    rw [ofConv_toConv, hf, ofConv_sum, LinearMap.sum_apply]
    simp only [hj])
  have h0 := natCast_eq_zero_of_algebra h (WithConv (A →ₗ[R] B))
  rw [e, ← frobRing_apply h0, map_sum, ofConv_sum, LinearMap.sum_apply]
  simp only [frobRing_apply, smul_pow, ← map_pow, hj]

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} [hp : Fact p.Prime] {R S : Type} [CommRing R] [CommRing S]

theorem prime_smul_id_app (G : PDivGroup p R) (n : ℕ) (a : G.A n) :
    Hom.app ((p : ℤ_[p]) • 𝟙 G) n a = mulBy R _ p a := by rw [natCast_smul_id_app]

theorem eq_zero_of_prime_smul_eq_zero {G H : PDivGroup p R} {f : G ⟶ H}
    (e : (p : ℤ_[p]) • f = 0) : f = 0 := by
  have e' : ((p : ℤ_[p]) • 𝟙 G) ≫ f = ((p : ℤ_[p]) • 𝟙 G) ≫ 0 := by
    rw [Linear.smul_comp, Category.id_comp, e, Limits.comp_zero]
  refine hom_ext fun n => BialgHom.ext fun a => Test.mulP_injective G n ?_
  obtain ⟨b, rfl⟩ := H.res_surjective n a
  rw [← res_app, ← res_app, mulP_res, mulP_res, ← prime_smul_id_app, ← prime_smul_id_app]
  exact congrArg (fun g => Hom.app g (n + 1) b) e'

theorem SemiHom.rigExtMap_lift_comp_liftSemi [Algebra R S] {G : PDivGroup p R} {G' : PDivGroup p S}
    (s : SemiHom (algebraMap R S) G' G) :
    rigExtMap s.lift ∘ₗ liftSemi (G.toBase S).rig = liftSemi s.rig :=
  LinearMap.ext fun y => by
    induction y with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r x =>
      rw [LinearMap.comp_apply, liftSemi_tmul, liftSemi_tmul, map_smul, ← SemiHom.ofHom_rig,
        (G.toBase S).rig_rig _ s fun n a => ((s.lift_app n 1 a).trans (one_smul _ _)).symm]

variable (h : (p : R) = 0) (G : PDivGroup p R)

theorem verschiebung_app_eq_sum (n : ℕ) {ι : Type} (s : Finset ι) (φ : ι → CartierDual R (G.A n))
    (e : ι → G.A n) (hs : ∀ a, ∑ i ∈ s, φ i a • e i = a) (a : G.A n) :
    (verschiebung h G).app n a = ∑ i ∈ s, (φ i ^ p) a • (frobProj h G).app n (e i) :=
  frobTwist_ext_dual h n fun χ => by
    rw [frobTwistDual_verschiebung, map_sum]
    refine (convPow_prime_apply h s φ (fun i => χ (e i)) χ.ofConv
      (fun a => by simpa only [map_sum, map_smul] using congrArg χ.ofConv (hs a).symm) a).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_smul, frobTwistDual_frobProj]

theorem relFrob_app_verschiebung_app (n : ℕ) (a : G.A n) :
    (relFrob h G).app n ((verschiebung h G).app n a) = mulBy R _ p a := by
  obtain ⟨s, hs⟩ := exists_dualSystem R (G.A n)
  rw [verschiebung_app_eq_sum h G n s Prod.fst Prod.snd hs, map_sum]
  simp only [map_smul, relFrob_app_frobProj]
  refine (convPow_prime_apply h s Prod.fst Prod.snd LinearMap.id (fun a => (hs a).symm) a).symm.trans ?_
  exact (congrArg (fun f => f.ofConv a)
    (BialgHom.toLinearMap_convPow (toConv (BialgHom.id R (G.A n))) p)).symm

theorem relFrob_comp_verschiebung : relFrob h G ≫ verschiebung h G = (p : ℤ_[p]) • 𝟙 G :=
  hom_ext fun n => BialgHom.ext fun a =>
    (relFrob_app_verschiebung_app h G n a).trans (prime_smul_id_app G n a).symm

theorem frobProj_app_relFrob_app (n : ℕ) (x : (frobTwist h G).A n) :
    (frobProj h G).app n ((relFrob h G).app n x) = x ^ p := by
  rw [← absFrob_app h]
  induction x using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => simp only [map_add, hx, hy]
  | h1 r a =>
    rw [map_smul, SemiBialgHom.smul_map, SemiBialgHom.smul_map, relFrob_app_frobProj, map_pow,
      absFrob_app]

theorem verschiebung_comp_relFrob :
    verschiebung h G ≫ relFrob h G = (p : ℤ_[p]) • 𝟙 (frobTwist h G) :=
  frobTwist_hom_ext h fun n a => by
    rw [prime_smul_id_app, ← SemiBialgHom.map_mulBy, ← relFrob_app_verschiebung_app h,
      frobProj_app_relFrob_app, ← map_pow, ← relFrob_app_frobProj h]
    rfl

variable {G}

theorem epi_relFrob : Epi (relFrob h G) :=
  Preadditive.epi_of_cancel_zero _ fun g e => eq_zero_of_prime_smul_eq_zero (by
    rw [← Category.id_comp g, ← Linear.smul_comp, ← verschiebung_comp_relFrob, Category.assoc, e,
      Limits.comp_zero])

theorem mono_relFrob : Mono (relFrob h G) :=
  Preadditive.mono_of_cancel_zero _ fun g e => eq_zero_of_prime_smul_eq_zero (by
    rw [← Category.comp_id g, ← Linear.comp_smul, ← relFrob_comp_verschiebung h, ← Category.assoc, e,
      Limits.zero_comp])

theorem eq_verschiebung_of_relFrob_comp {v : frobTwist h G ⟶ G}
    (e : relFrob h G ≫ v = (p : ℤ_[p]) • 𝟙 G) : v = verschiebung h G :=
  haveI := epi_relFrob h (G := G)
  (cancel_epi _).1 (e.trans (relFrob_comp_verschiebung h G).symm)

theorem eq_verschiebung_of_comp_relFrob {v : frobTwist h G ⟶ G}
    (e : v ≫ relFrob h G = (p : ℤ_[p]) • 𝟙 _) : v = verschiebung h G :=
  haveI := mono_relFrob h (G := G)
  (cancel_mono _).1 (e.trans (verschiebung_comp_relFrob h G).symm)

section Naturality

variable (h' : (p : S) = 0) {σ : R →+* S} {G' : PDivGroup p S} (s : SemiHom σ G' G)

theorem SemiHom.app_relFrob (n : ℕ) (x : (PDivGroup.frobTwist h G).A n) :
    s.app n ((relFrob h G).app n x) = (relFrob h' G').app n ((s.frobTwist h h').app n x) := by
  induction x using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => simp only [map_add, hx, hy]
  | h1 r a =>
    rw [map_smul, SemiBialgHom.smul_map, SemiBialgHom.smul_map, map_smul, relFrob_app_frobProj,
      SemiHom.frobTwist_app_frobProj, relFrob_app_frobProj, map_pow]

theorem SemiHom.app_verschiebung (n : ℕ) (a : G.A n) :
    (s.frobTwist h h').app n ((verschiebung h G).app n a) =
      (verschiebung h' G').app n (s.app n a) := by
  refine Test.mulP_injective (PDivGroup.frobTwist h' G') n ?_
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [← PDivGroup.res_app, ← SemiHom.res_app, ← SemiHom.res_app, ← PDivGroup.res_app, mulP_res,
    mulP_res, ← map_mulBy,
    ← SemiBialgHom.map_mulBy (s.app _), ← relFrob_app_verschiebung_app h, s.app_relFrob h h',
    ← prime_smul_id_app, ← verschiebung_comp_relFrob]
  rfl

variable {H : PDivGroup p R}

theorem relFrob_naturality (f : G ⟶ H) : f ≫ relFrob h H = relFrob h G ≫ frobTwistMap h f :=
  frobTwist_hom_ext h fun n a => by
    change f.app n ((relFrob h H).app n _) = (relFrob h G).app n ((frobTwistMap h f).app n _)
    rw [frobTwistMap_app_frobProj, relFrob_app_frobProj, relFrob_app_frobProj, map_pow]

theorem verschiebung_naturality (f : G ⟶ H) :
    frobTwistMap h f ≫ verschiebung h H = verschiebung h G ≫ f := by
  haveI := epi_relFrob h (G := G)
  rw [← cancel_epi (relFrob h G), ← Category.assoc, ← relFrob_naturality, Category.assoc,
    ← Category.assoc (relFrob h G), relFrob_comp_verschiebung, relFrob_comp_verschiebung,
    Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

variable (G) [Algebra R S]

theorem relFrob_baseChange : relFrob h' (G.baseChange S) ≫ (frobTwistBaseChange h G h').hom =
    baseChangeMap S (relFrob h G) :=
  baseChange_hom_ext fun n x =>
    (congrArg ((relFrob h' (G.baseChange S)).app n) (frobTwistBaseChange_hom_app h G h' n x)).trans
      ((G.toBase S).app_relFrob h h' n x).symm

theorem verschiebung_baseChange : (frobTwistBaseChange h G h').hom ≫
    baseChangeMap S (verschiebung h G) = verschiebung h' (G.baseChange S) :=
  baseChange_hom_ext fun n a =>
    (frobTwistBaseChange_hom_app h G h' n _).trans ((G.toBase S).app_verschiebung h h' n a)

end Naturality

variable (G)

theorem dualHom_verschiebung :
    dualHom _ _ (verschiebung h G) ≫ (frobTwistDual h G).hom = relFrob h G.dual :=
  frobTwist_hom_ext h fun n χ => (CartierDual.ext_apply fun a =>
    frobTwistDual_verschiebung h n χ a).trans (relFrob_app_frobProj h (G := G.dual) n χ).symm

theorem dualHom_relFrob :
    (frobTwistDual h G).hom ≫ verschiebung h G.dual = dualHom _ _ (relFrob h G) := by
  rw [← Iso.eq_inv_comp]
  refine (eq_verschiebung_of_relFrob_comp h ?_).symm
  rw [← dualHom_verschiebung, Category.assoc, Iso.hom_inv_id_assoc, ← dualHom_comp,
    relFrob_comp_verschiebung, map_smul, dualHom_id]

theorem omegaMap_relFrob : omegaMap _ _ (relFrob h G) = 0 :=
  LinearMap.ext fun w => Subtype.ext (funext fun n => by
    obtain ⟨x, hx⟩ := AugCot.d_surjective _ (w.1 n)
    rw [omegaMap_val, ← hx, cotMap_d]
    change dUnit R _ = 0
    clear hx
    induction x using frobTwist_induction h n with
    | h0 => simp only [map_zero]
    | h2 x y hx hy => simp only [map_add, hx, hy, add_zero]
    | h1 r a => rw [map_smul, relFrob_app_frobProj, dUnit, map_smul, ← dUnit, dUnit_pow_prime h, smul_zero])

theorem rigExtMap_relFrob_comp_rigOfOmega :
    rigExtMap (relFrob h G) ∘ₗ (frobTwist h G).rigOfOmega = 0 :=
  LinearMap.ext fun w => by
    rw [LinearMap.comp_apply, rigExtMap_rigOfOmega, omegaMap_relFrob, LinearMap.zero_apply, map_zero,
      LinearMap.zero_apply]

theorem verschiebung_app_eq_zero (n : ℕ) {b : G.A n} (hb : cobOne R _ b = 0) :
    (verschiebung h G).app n b = 0 :=
  frobTwist_ext_dual h n fun χ => by
    rw [frobTwistDual_verschiebung, map_zero, ← primTangent_d ⟨b, hb⟩, dUnit_pow_prime h, map_zero]

theorem vecExtMap_verschiebung : vecExtMap (verschiebung h G) = 0 :=
  LinearMap.ext fun x => ((frobTwist h G).extChar_bijective h).1 (Subtype.ext (by
    rw [extChar_vecExtMap h, verschiebung_app_eq_zero h G 1 (G.extChar h x).2, LinearMap.zero_apply,
      map_zero]
    rfl))

theorem range_rigExtMap_verschiebung_le :
    LinearMap.range (rigExtMap (verschiebung h G)) ≤ LinearMap.range (frobTwist h G).rigOfOmega := by
  rintro _ ⟨x, rfl⟩
  refine ((frobTwist h G).exact_rigOfOmega_rigToExt _).1 ?_
  rw [rigToExt_rigExtMap, vecExtMap_verschiebung, LinearMap.zero_apply]

theorem rigExtMap_relFrob_rig (x : G.RigExt) :
    rigExtMap (relFrob h G) ((frobProj h G).rig x) = (absFrob h G).rig x := by
  rw [← SemiHom.ofHom_rig]
  exact (frobProj h G).rig_rig _ _
    (fun n a => (absFrob_app h G n a).trans (relFrob_app_frobProj h n a).symm) x

theorem rigExtMap_relFrob_comp_liftSemi :
    letI := (frobRing h).toAlgebra
    rigExtMap (relFrob h G) ∘ₗ liftSemi (R := R) (R' := R) (frobProj h G).rig =
      liftSemi (R := R) (R' := R) (absFrob h G).rig :=
  letI := (frobRing h).toAlgebra
  SemiHom.rigExtMap_lift_comp_liftSemi (R := R) (S := R) (absFrob h G)

section Perfect

variable {k : Type} [Field k] [CharP k p]

theorem ker_rigExtMap_eq_range
    (hW : ∃ (M : PDivGroup p k → ModuleCat.{0} (WittVector p k))
      (map : ∀ G H : PDivGroup p k, (G ⟶ H) →+ (M H →ₗ[WittVector p k] M G))
      (red : ∀ G : PDivGroup p k,
        M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt),
      (∀ G : PDivGroup p k, Module.Free (WittVector p k) (M G) ∧ Module.Finite (WittVector p k) (M G) ∧
        Module.finrank (WittVector p k) (M G) = G.height ∧ Function.Surjective (red G) ∧
        (∀ m, red G m = 0 ↔ ∃ n, m = p • n) ∧ map G G (𝟙 G) = LinearMap.id) ∧
      (∀ (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K),
        map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
      ∀ (G H : PDivGroup p k) (f : G ⟶ H) (m : M H),
        red G (map G H f m) = PDivGroup.rigExtMap f (red H m))
    {G H : PDivGroup p k} {f : G ⟶ H} {g : H ⟶ G} (hf : f ≫ g = (p : ℤ_[p]) • 𝟙 G)
    (hg : g ≫ f = (p : ℤ_[p]) • 𝟙 H) :
    LinearMap.ker (rigExtMap f) = LinearMap.range (rigExtMap g) := by
  obtain ⟨M, map, red, h1, h2, h3⟩ := hW
  have hm : ∀ (K : PDivGroup p k) (m : M K), map K K ((p : ℤ_[p]) • 𝟙 K) m = p • m := fun K m => by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, (h1 K).2.2.2.2.2, LinearMap.smul_apply, LinearMap.id_apply]
  refine Submodule.ext fun x => ?_
  obtain ⟨m, rfl⟩ := (h1 H).2.2.2.1 x
  rw [LinearMap.mem_ker, ← h3, (h1 G).2.2.2.2.1]
  constructor
  · rintro ⟨n, hn⟩
    have := (h1 H).1
    have e : (p : WittVector p k) • m = (p : WittVector p k) • map H G g n := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← map_nsmul, ← hn, ← hm, ← hg, h2,
        LinearMap.comp_apply]
    exact ⟨red G n, by rw [← h3, smul_right_injective _ (WittVector.p_nonzero p k) e]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := (h1 G).2.2.2.1 y
    rw [← (h1 G).2.2.2.2.1, h3, ← hy, ← h3, ← h3, ← LinearMap.comp_apply (map G H f), ← h2, hf, hm,
      (h1 G).2.2.2.2.1]
    exact ⟨n, rfl⟩

end Perfect

theorem frobenius_verschiebung (p : ℕ) [Fact p.Prime] :
    (∀ ⦃R : Type⦄ [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R),
      relFrob h G ≫ verschiebung h G = (p : ℤ_[p]) • 𝟙 G ∧
      verschiebung h G ≫ relFrob h G = (p : ℤ_[p]) • 𝟙 (frobTwist h G) ∧
      (∀ (H : PDivGroup p R) (f : G ⟶ H), (p : ℤ_[p]) • f = 0 → f = 0) ∧
      (∀ v : frobTwist h G ⟶ G, relFrob h G ≫ v = (p : ℤ_[p]) • 𝟙 G → v = verschiebung h G) ∧
      (∀ (H : PDivGroup p R) (f : G ⟶ H), f ≫ relFrob h H = relFrob h G ≫ frobTwistMap h f ∧
        frobTwistMap h f ≫ verschiebung h H = verschiebung h G ≫ f) ∧
      (∀ ⦃S : Type⦄ [CommRing S] (h' : (p : S) = 0) (σ : R →+* S) (G' : PDivGroup p S)
        (s : SemiHom σ G' G) (n : ℕ),
        (∀ x, s.app n ((relFrob h G).app n x) = (relFrob h' G').app n ((s.frobTwist h h').app n x)) ∧
        ∀ a, (s.frobTwist h h').app n ((verschiebung h G).app n a) =
          (verschiebung h' G').app n (s.app n a)) ∧
      (∀ (S : Type) [CommRing S] [Algebra R S] (h' : (p : S) = 0),
        relFrob h' (G.baseChange S) ≫ (frobTwistBaseChange h G h').hom =
          baseChangeMap S (relFrob h G) ∧
        (frobTwistBaseChange h G h').hom ≫ baseChangeMap S (verschiebung h G) =
          verschiebung h' (G.baseChange S)) ∧
      rigExtMap (relFrob h G) ∘ₗ (frobTwist h G).rigOfOmega = 0 ∧
      vecExtMap (verschiebung h G) = 0 ∧
      (∀ (r : R) (x : G.RigExt),
        rigExtMap (relFrob h G) (r • (frobProj h G).rig x) = r • (absFrob h G).rig x)) ∧
    ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p],
      (∃ (M : PDivGroup p k → ModuleCat.{0} (WittVector p k))
        (map : ∀ G H : PDivGroup p k, (G ⟶ H) →+ (M H →ₗ[WittVector p k] M G))
        (red : ∀ G : PDivGroup p k,
          M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt),
        (∀ G : PDivGroup p k, Module.Free (WittVector p k) (M G) ∧
          Module.Finite (WittVector p k) (M G) ∧
          Module.finrank (WittVector p k) (M G) = G.height ∧ Function.Surjective (red G) ∧
          (∀ m, red G m = 0 ↔ ∃ n, m = p • n) ∧ map G G (𝟙 G) = LinearMap.id) ∧
        (∀ (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K),
          map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
        ∀ (G H : PDivGroup p k) (f : G ⟶ H) (m : M H),
          red G (map G H f m) = PDivGroup.rigExtMap f (red H m)) →
      (∀ (G H : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) • 𝟙 G →
        g ≫ f = (p : ℤ_[p]) • 𝟙 H → LinearMap.ker (rigExtMap f) = LinearMap.range (rigExtMap g)) ∧
      ∀ (h : (p : k) = 0) (G : PDivGroup p k),
        LinearMap.ker (rigExtMap (relFrob h G)) = LinearMap.range (rigExtMap (verschiebung h G)) ∧
        LinearMap.ker (rigExtMap (verschiebung h G)) = LinearMap.range (rigExtMap (relFrob h G)) :=
  ⟨fun _ _ h G => ⟨relFrob_comp_verschiebung h G, verschiebung_comp_relFrob h G,
      fun _ _ => eq_zero_of_prime_smul_eq_zero, fun _ => eq_verschiebung_of_relFrob_comp h,
      fun _ f => ⟨relFrob_naturality h f, verschiebung_naturality h f⟩,
      fun _ _ h' _ _ s n => ⟨s.app_relFrob h h' n, s.app_verschiebung h h' n⟩,
      fun _ _ _ h' => ⟨relFrob_baseChange h G h', verschiebung_baseChange h G h'⟩,
      rigExtMap_relFrob_comp_rigOfOmega h G, vecExtMap_verschiebung h G,
      fun r x => by rw [map_smul, rigExtMap_relFrob_rig]⟩,
    fun _ _ _ _ hW => ⟨fun _ _ _ _ => ker_rigExtMap_eq_range hW, fun h G =>
      ⟨ker_rigExtMap_eq_range hW (relFrob_comp_verschiebung h G) (verschiebung_comp_relFrob h G),
        ker_rigExtMap_eq_range hW (verschiebung_comp_relFrob h G) (relFrob_comp_verschiebung h G)⟩⟩⟩

end PDivGroup

end GlobalTheory
