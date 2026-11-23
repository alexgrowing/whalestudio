import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProdInjectiveBirigidifiedGaloisIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubFiniteFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreMulKTorsorHarrisTaylorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke.Comp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

theorem eta_nsmul {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (n : ℕ) (x : D.La) :
    o.eta (n • x) = o.eta x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem transl_one' {A : Over S} [GrpObj A] : transl (1 : 𝟙_ (Over S) ⟶ A) = 𝟙 A := by
  rw [transl, comp_one, _root_.mul_one]

theorem comp_transl {T A : Over S} [GrpObj A] (y : T ⟶ A) (a : 𝟙_ (Over S) ⟶ A) :
    y ≫ transl a = y * (toUnit T ≫ a) := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem transl_mul' {A : Over S} [GrpObj A] (a c : 𝟙_ (Over S) ⟶ A) :
    transl (a * c) = transl a ≫ transl c := by
  rw [comp_transl, transl, transl, comp_mul, _root_.mul_assoc]

theorem transl_pow {A : Over S} [GrpObj A] [IsCommMonObj A] (a : 𝟙_ (Over S) ⟶ A) (k : ℕ) (ha : a ^ k = 1) :
    transl a ≫ ((𝟙 A) ^ k) = (𝟙 A) ^ k := by
  rw [comp_pow, Category.comp_id, transl, mul_pow, ← comp_pow, ha, comp_one, _root_.mul_one]

theorem isUnit_natCast (b : Base D R) (s : S ⟶ Sp R) (k : ℕ) (hk : k.Coprime p) : IsUnit ((k : ℕ) : Γ(S, ⊤)) := by
  have h1 := (b.unit k hk).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
  simpa using h1

end GlobalTheory.UPel.HT.Hecke.Comp

namespace GlobalTheory.UPel.HT.Hecke.Comp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

theorem pow_eq_one_of_mem {k N : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k * k) s) (h : 𝟙_ (Over S) ⟶ o.A)
    (hh : h ∈ heckeSub o LinearMap.id (N * k)) : h ^ k = 1 := by
  obtain ⟨x, rfl⟩ := hh
  rw [← eta_nsmul, smul_smul, mul_comm k, o.eta_ker]

theorem isGaloisCover_pow (k N : ℕ) (hk : 0 < k) (hN : 0 < N) (hkp : k.Coprime p) (hNp : N.Coprime p)
    (s : S ⟶ Sp R) (o : Obj b (N * k * k) s)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ o.A.left),
      y ≫ ((𝟙 o.A) ^ k).left = y' ≫ ((𝟙 o.A) ^ k).left →
        ∃! a : heckeSub o LinearMap.id (N * k), y ≫ (transl a.1).left = y') :
    GlobalTheory.ZM.IsGaloisCover (heckeSub o LinearMap.id (N * k)) (fun h => (transl h.1).left) ((𝟙 o.A) ^ k).left := by
  obtain ⟨-, hfin, het, hsurj⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S o.A k o.ab
    (isUnit_natCast b s k hkp)
  refine ⟨(heckeSub_finite_free p D R b LinearMap.id k (N * k) hk (Nat.mul_pos hN hk) hkp
      (Nat.Coprime.mul hNp hkp) S s o).1, ?_, ?_, ?_, hfin, het, hsurj, hfib⟩
  · show (transl (1 : 𝟙_ (Over S) ⟶ o.A)).left = 𝟙 _
    rw [transl_one']; rfl
  · intro a c
    show (transl (a.1 * c.1)).left = _
    rw [transl_mul']; rfl
  · intro a
    show (transl a.1 ≫ ((𝟙 o.A) ^ k)).left = _
    rw [transl_pow _ k (pow_eq_one_of_mem o a.1 a.2)]

end GlobalTheory.UPel.HT.Hecke.Comp

namespace GlobalTheory.UPel.HT.Hecke.Comp

variable {S : Scheme.{0}}

theorem cls_lbPow' {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (m : ℕ) (h : (GlobalTheory.UPel.HT.Hecke.lbPow L m).IsLB) :
    GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L m) h = m • GlobalTheory.CechPic.cls L hL := by
  refine (GlobalTheory.CechPic.cls_linComb hL _ _ h).trans ?_
  simp [GlobalTheory.CechPic.pull_id]

theorem grpSchemeSquareProductMap_comp {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C]
    [IsCommMonObj C] (f : A ⟶ B) (g : B ⟶ C) :
    GlobalTheory.UPel.HT.Hecke.sq2 (f ≫ g) = GlobalTheory.UPel.HT.Hecke.sq2 f ≫ GlobalTheory.UPel.HT.Hecke.sq2 g := by
  simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left]
  congr 1
  ext <;> simp

theorem grpSchemeSquareProductMap_fst {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (f : A ⟶ B) :
    GlobalTheory.UPel.HT.Hecke.sq2 f ≫ (fst B B).left = (fst A A).left ≫ f.left := by
  simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left, lift_fst]

theorem grpSchemeSquareProductMap_snd {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (f : A ⟶ B) :
    GlobalTheory.UPel.HT.Hecke.sq2 f ≫ (snd B B).left = (snd A A).left ≫ f.left := by
  simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left, lift_snd]

theorem lift_one_id_grpSchemeSquareProductMap {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (f : A ⟶ B)
    [IsMonHom f] : (lift (1 : A ⟶ A) (𝟙 A)).left ≫ GlobalTheory.UPel.HT.Hecke.sq2 f = f.left ≫ (lift (1 : B ⟶ B) (𝟙 B)).left := by
  simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left]
  congr 1
  ext <;> simp

theorem lift_id_one_grpSchemeSquareProductMap {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (f : A ⟶ B)
    [IsMonHom f] : (lift (𝟙 A) (1 : A ⟶ A)).left ≫ GlobalTheory.UPel.HT.Hecke.sq2 f = f.left ≫ (lift (𝟙 B) (1 : B ⟶ B)).left := by
  simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left]
  congr 1
  ext <;> simp

end GlobalTheory.UPel.HT.Hecke.Comp

namespace GlobalTheory.UPel.HT.Hecke.Comp

theorem nonempty_objMap_forget : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (o₁ : Obj b (N * k) s) (o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o₁.A ⟶ o₂.A), IsHecke g' c' k (N * k) o o₁ ψ₁ → IsHecke g c k N o₁ o₂ ψ₂ → Nonempty (ObjMap (o.forget N ⟨k * k, by ring⟩ hc) o₂ (𝟙 S)) := by
  intro p _ D R _ b g g' c c' k N hkp hN3 hNp hgg' hg'g hcc' hc S s o o₁ o₂ ψ₁ ψ₂ h₁ h₂
  obtain ⟨hm₁, ha₁, he₁, hG₁, ⟨hP₁⟩, -⟩ := h₁
  obtain ⟨hm₂, ha₂, he₂, hG₂, ⟨hP₂⟩, -⟩ := h₂
  have hk : 0 < k := Nat.pos_of_ne_zero (by
    rintro rfl; exact (Fact.out : p.Prime).one_lt.ne' ((Nat.coprime_zero_left p).1 hkp))
  have hN : 0 < N := by omega
  have hfibAll : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ o.A.left), y ≫ ((𝟙 o.A) ^ k).left = y' ≫ ((𝟙 o.A) ^ k).left → ∃! a : GlobalTheory.UPel.HT.Hecke.heckeSub o LinearMap.id (N * k), y ≫ (GlobalTheory.UPel.HT.Hecke.transl a.1).left = y' := GlobalTheory.T.geometric_fibre_mulK_torsor_harrisTaylor
  have hbil : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, LBIso (GlobalTheory.UPel.HT.Hecke.lbPow P (n ^ 2)) (P.pull (GlobalTheory.UPel.HT.Hecke.sq2 ((𝟙 A) ^ n))) := GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple
  have hGal := isGaloisCover_pow k N hk hN hkp hNp s o (hfibAll p D R b k N hk hN hkp hNp S s o)
  obtain ⟨hKm, -, -, -⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S o.A k o.ab (isUnit_natCast b s k hkp)
  have hχ : ∀ h ∈ heckeSub o LinearMap.id (N * k), h ≫ (ψ₁ ≫ ψ₂) = 1 := by
    rintro _ ⟨x, rfl⟩
    show o.eta ((N * k) • x) ≫ (ψ₁ ≫ ψ₂) = 1
    have e : o.eta ((N * k) • x) ≫ ψ₁ = o₁.eta (N • g x) := by
      rw [he₁, map_nsmul, hg'g, smul_smul]
    rw [← Category.assoc, e]
    exact comp_eq_one_of_transl ψ₂ _ (hG₂.inv ⟨_, mem_heckeSub o₁ g N x⟩)
  obtain ⟨φ, hφm, hφ⟩ := GlobalTheory.HomDescent.exists_desc S o.A o.A o₂.A _ ((𝟙 o.A) ^ k) hKm hGal (ψ₁ ≫ ψ₂)
    inferInstance hχ
  obtain ⟨f₁, hf₁m, hf₁⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₁.A o.A _ ψ₁ hm₁ hG₁ ((𝟙 o.A) ^ k) hKm (by
    rintro _ ⟨x, rfl⟩
    rw [comp_pow, Category.comp_id, ← eta_nsmul, smul_smul, mul_comm k, o.eta_ker])
  obtain ⟨θ, hθm, hθ⟩ := GlobalTheory.HomDescent.exists_desc S o₁.A o₂.A o.A _ ψ₂ hm₂ hG₂ f₁ hf₁m (by
    rintro _ ⟨y, rfl⟩
    rw [he₁, Category.assoc, hf₁, comp_pow, Category.comp_id, ← eta_nsmul, map_nsmul, hg'g, smul_smul, smul_smul,
      mul_comm k N, o.eta_ker])
  have hKe : Epi ((𝟙 o.A) ^ k).left := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hGal
  have hKeO : Epi ((𝟙 o.A) ^ k) := (Over.forget S).epi_of_epi_map hKe
  have hχe : Epi (ψ₁ ≫ ψ₂).left := by
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hG₁
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hG₂
    rw [Over.comp_left]; infer_instance
  have hχeO : Epi (ψ₁ ≫ ψ₂) := (Over.forget S).epi_of_epi_map hχe
  have e1 : φ ≫ θ = 𝟙 o.A := by
    rw [← cancel_epi ((𝟙 o.A) ^ k), ← Category.assoc, hφ, Category.assoc, hθ, hf₁, Category.comp_id]
  have e2 : θ ≫ φ = 𝟙 o₂.A := by
    rw [← cancel_epi (ψ₁ ≫ ψ₂), Category.comp_id, Category.assoc, reassoc_of% hθ, ← Category.assoc, hf₁, hφ]
  let e : o.A ≅ o₂.A := ⟨φ, θ, e1, e2⟩
  haveI : IsMonHom e.hom := hφm
  have hχa : ∀ c0, o.act.act c0 ≫ ψ₁ ≫ ψ₂ = (ψ₁ ≫ ψ₂) ≫ o₂.act.act c0 := fun c0 => by
    rw [reassoc_of% (ha₁ c0), ha₂ c0, Category.assoc]
  have hpol : LBIso o.P (o₂.P.pull (sq2 φ)) := by
    have hQ₂ : (o₂.P.pull (sq2 φ)).IsLB := pull_isLB o₂.isLB _
    have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hcc'; have := pow_pos hk 2; omega)
    have hc'0 : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hcc'; have := pow_pos hk 2; omega)
    have hcc : k ^ 2 / c * (k ^ 2 / c') = k ^ 2 := by
      rw [Nat.div_eq_of_eq_mul_left hc0 (by rw [← hcc', mul_comm]), Nat.div_eq_of_eq_mul_left hc'0 hcc'.symm,
        mul_comm]
      exact hcc'
    have hL : ∀ m, (GlobalTheory.UPel.HT.Hecke.lbPow o.P m).IsLB := fun m => LB.isLB_linComb o.isLB _ _
    have hL₁ : ∀ m, (GlobalTheory.UPel.HT.Hecke.lbPow o₁.P m).IsLB := fun m => LB.isLB_linComb o₁.isLB _ _
    have E₁ := (GlobalTheory.CechPic.cls_eq_iff (hL _) (pull_isLB o₁.isLB _)).2 hP₁
    have E₂ := (GlobalTheory.CechPic.cls_eq_iff (hL₁ _) (pull_isLB o₂.isLB _)).2 hP₂
    have E₀ := (GlobalTheory.CechPic.cls_eq_iff (hL _) (pull_isLB o.isLB _)).2
      (hbil S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.ample k)
    rw [cls_lbPow' o.isLB, GlobalTheory.CechPic.cls_pull o₁.isLB] at E₁
    rw [cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₂.isLB] at E₂
    rw [cls_lbPow' o.isLB, GlobalTheory.CechPic.cls_pull o.isLB] at E₀
    have c2₁ : GlobalTheory.CechPic.pull (lift (1 : o₂.A ⟶ o₂.A) (𝟙 _)).left (GlobalTheory.CechPic.cls o₂.P o₂.isLB) = 0 := by
      rw [← GlobalTheory.CechPic.cls_pull o₂.isLB _ (pull_isLB o₂.isLB _)]
      exact (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o₂.rig₁
    have c2₂ : GlobalTheory.CechPic.pull (lift (𝟙 _) (1 : o₂.A ⟶ o₂.A)).left (GlobalTheory.CechPic.cls o₂.P o₂.isLB) = 0 := by
      rw [← GlobalTheory.CechPic.cls_pull o₂.isLB _ (pull_isLB o₂.isLB _)]
      exact (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o₂.rig₂
    refine GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A o.A _ ((𝟙 o.A) ^ k) o.ab o.ab hKm hGal o.P _ o.isLB hQ₂ o.rig₁ o.rig₂ ?_ ?_ ?_
    · refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ₂ _)).1 ?_
      rw [GlobalTheory.CechPic.cls_pull hQ₂, GlobalTheory.CechPic.cls_pull o₂.isLB, ← GlobalTheory.CechPic.pull_comp, lift_one_id_grpSchemeSquareProductMap,
        GlobalTheory.CechPic.pull_comp, c2₁, map_zero]
    · refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ₂ _)).1 ?_
      rw [GlobalTheory.CechPic.cls_pull hQ₂, GlobalTheory.CechPic.cls_pull o₂.isLB, ← GlobalTheory.CechPic.pull_comp, lift_id_one_grpSchemeSquareProductMap,
        GlobalTheory.CechPic.pull_comp, c2₂, map_zero]
    · refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB o.isLB _) (pull_isLB hQ₂ _)).1 ?_
      rw [GlobalTheory.CechPic.cls_pull o.isLB, GlobalTheory.CechPic.cls_pull hQ₂, GlobalTheory.CechPic.cls_pull o₂.isLB,
        ← GlobalTheory.CechPic.pull_comp, ← grpSchemeSquareProductMap_comp, hφ, grpSchemeSquareProductMap_comp, GlobalTheory.CechPic.pull_comp, ← E₂, map_nsmul, ← E₁,
        smul_smul, hcc, E₀]
  refine ⟨⟨φ.left, sq2 φ, isGrpPullback_of_iso e, ⟨grpSchemeSquareProductMap_fst φ, grpSchemeSquareProductMap_snd φ⟩, ?_, hpol, ?_⟩⟩
  · intro c0
    show (o.act.act c0).left ≫ φ.left = φ.left ≫ (o₂.act.act c0).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    haveI := o.act.hom c0
    have hKcomm : ((𝟙 o.A) ^ k) ≫ o.act.act c0 = o.act.act c0 ≫ ((𝟙 o.A) ^ k) := by
      rw [pow_comp, comp_pow, Category.id_comp, Category.comp_id]
    rw [← cancel_epi ((𝟙 o.A) ^ k), ← Category.assoc, hKcomm, Category.assoc, hφ, hχa, ← hφ,
      Category.assoc]
  · intro y
    show (o.eta (((N * k * k) / N) • y)).left ≫ φ.left = 𝟙 S ≫ (o₂.eta y).left
    have hd : N * k * k / N = k * k := by rw [_root_.mul_assoc, Nat.mul_div_cancel_left _ hN]
    rw [hd, Category.id_comp, ← Over.comp_left]
    congr 1
    rw [he₂, he₁, hg'g, Category.assoc, ← hφ, ← Category.assoc, comp_pow, Category.comp_id, ← eta_nsmul, smul_smul]

end GlobalTheory.UPel.HT.Hecke.Comp
