import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRedDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupBaseChangeIsConnIsEtPerfect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneBaseChangeBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem addHom_eq_of_basis {R S M ι : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (ρ : R →+* S) (F₁ F₂ : M →+ S)
    (h₁ : ∀ (c : R) x, F₁ (c • x) = ρ c * F₁ x) (h₂ : ∀ (c : R) x, F₂ (c • x) = ρ c * F₂ x)
    (h : ∀ i, F₁ (b i) = F₂ (b i)) (x : M) : F₁ x = F₂ x := by
  have hx : x ∈ Submodule.span R (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul c y _ hy => rw [h₁, h₂, hy]

theorem wittMap_comp (p : ℕ) [Fact p.Prime] {k k' k'' : Type} [CommRing k] [CommRing k'] [CommRing k'']
    (σ : k →+* k') (τ : k' →+* k'') (x : WittVector p k) :
    WittVector.map (τ.comp σ) x = WittVector.map τ (WittVector.map σ x) := by
  ext n
  simp [WittVector.map_coeff]

end GlobalTheory.Dieu.EtFromConn

theorem GlobalTheory.Dieu.EtFromConn.isTr_comp : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' k'' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Field k''] [CharP k'' p] [PerfectRing k'' p] (σ : k →+* k') (τ : k' →+* k'') (υ : k →+* k'') (G'' : PDivGroup p k'') (G' : PDivGroup p k') (G : PDivGroup p k) (h'' : G''.IsEt) (h' : G'.IsEt) (h : G.IsEt) (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G), (∀ n a, u.app n a = t.app n (s.app n a)) → ∀ (l : Mod B G h) (l' : Mod B G' h') (l'' : Mod B G'' h''), IsTr B σ h' h s l l' → IsTr B τ h'' h' t l' l'' → IsTr B υ h'' h u l l'' := by
  intro p _ B k k' k'' _ _ _ _ _ _ _ _ _ σ τ υ G'' G' G h'' h' h s t u hu l l' l'' hs ht
  have hυ : υ = τ.comp σ := by
    ext r
    have e := congrArg (Coalgebra.counit (R := k'')) (hu 0 (algebraMap k (G.A 0) r))
    rw [(u.app 0).counit_map, (t.app 0).counit_map, (s.app 0).counit_map,
      Bialgebra.counit_algebraMap] at e
    simpa using e
  subst hυ
  obtain rfl : u = t.comp s := SemiHom.ext_apply hu
  letI iσ : Algebra k k' := σ.toAlgebra
  letI iτ : Algebra k' k'' := τ.toAlgebra
  letI iυ : Algebra k k'' := (τ.comp σ).toAlgebra
  dsimp only [IsTr] at hs ht ⊢
  obtain ⟨hb, lb, hlb, hl'⟩ := hs
  obtain ⟨hb', lb', hlb', hl''⟩ := ht
  have hD := dual_conn h
  have hbu : (G.dual.baseChange k'').IsConn := (baseChange_isConn_isEt p k k'' G.dual).1 hD
  haveI := B.free G.dual hD
  haveI := B.finite G.dual hD
  let b := Module.Free.chooseBasis (WittVector p k) (B.M G.dual hD)
  obtain ⟨bu, hbu_eq⟩ := GlobalTheory.T.dieudonne_baseChange_basis p _ B k k'' G.dual hD hbu _ b
  obtain ⟨bk, hbk_eq⟩ := GlobalTheory.T.dieudonne_baseChange_basis p _ B k k' G.dual hD hb _ b
  let lbu : Module.Dual (WittVector p k'') (B.M (G.dual.baseChange k'') hbu) :=
    bu.constr (WittVector p k'') fun i => WittVector.map (τ.comp σ) (l (b i))
  have hlbu : ∀ x, lbu (B.smap hbu hD (G.dual.toBase k'') x) = WittVector.map (τ.comp σ) (l x) := by
    intro x
    refine addHom_eq_of_basis b (WittVector.map (τ.comp σ))
      ((lbu : _ →+ WittVector p k'').comp (B.smap hbu hD (G.dual.toBase k'')))
      ((WittVector.map (τ.comp σ)).toAddMonoidHom.comp (l : _ →+ WittVector p k)) ?_ ?_ ?_ x
    · intro c x
      show lbu (B.smap hbu hD (G.dual.toBase k'') (c • x)) = _ * lbu (B.smap hbu hD (G.dual.toBase k'') x)
      rw [B.smap_smul, LinearMap.map_smul, smul_eq_mul]
      rfl
    · intro c x
      simp [map_smul, smul_eq_mul, map_mul]
    · intro i
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_coe]
      rw [← hbu_eq, Module.Basis.constr_basis]
  refine ⟨hbu, lbu, hlbu, fun y => ?_⟩

  let β : G'.baseChange k'' ⟶ G.baseChange k'' :=
    SemiHom.lift (((G'.toBase k'').comp s : SemiHom ((algebraMap k' k'').comp σ) _ G) :
      SemiHom (algebraMap k k'') _ G)
  have hβ : ∀ n (b : G.A n), β.app n ((G.toBase k'').app n b) = (G'.toBase k'').app n (s.app n b) := by
    intro n b
    rw [toBase_app, SemiHom.lift_app, one_smul]
    rfl
  have hlift : (t.comp s).lift = t.lift ≫ β := baseChange_hom_ext fun n a => by
    rw [SemiHom.lift_app, one_smul, comp_app, BialgHom.comp_apply, ← toBase_app, hβ, toBase_app,
      SemiHom.lift_app, one_smul]
    rfl
  let φs := (PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift
  let φt := (PerfdLat.dualBaseChange k'' G').inv ≫ dualHom G'' (G'.baseChange k'') t.lift
  let ψ : G.dual.baseChange k'' ⟶ G'.dual.baseChange k'' :=
    (PerfdLat.dualBaseChange k'' G).inv ≫ dualHom _ _ β ≫ (PerfdLat.dualBaseChange k'' G').hom
  have hψ : (PerfdLat.dualBaseChange k'' G).inv ≫ dualHom G'' (G.baseChange k'') (t.comp s).lift =
      ψ ≫ φt := by
    simp only [hlift, dualHom_comp, ψ, φt, Category.assoc, Iso.hom_inv_id_assoc]
  let ρ : SemiHom τ (G.dual.baseChange k'') (G.dual.baseChange k') :=
    (G.dual.toBase k'').liftOver τ (fun _ => rfl)
  have hρ : ∀ n (χ : G.dual.A n), ρ.app n ((G.dual.toBase k').app n χ) = (G.dual.toBase k'').app n χ := by
    intro n χ
    rw [toBase_app, SemiHom.liftOver_app, map_one, one_smul]
  have hinv : ∀ {O' : Type} [Field O'] [Algebra k O'] (n : ℕ) (Z : (G.baseChange O').dual.A n),
      (PerfdLat.dualBaseChange O' G).hom.app n ((PerfdLat.dualBaseChange O' G).inv.app n Z) = Z :=
    fun {O'} _ _ n Z => DFunLike.congr_fun (congrArg (fun f => Hom.app f n) (PerfdLat.dualBaseChange O' G).hom_inv_id) Z
  have hinj : ∀ n, Function.Injective ((PerfdLat.dualBaseChange k'' G).hom.app n) := fun n x y hxy => by
    have e : ∀ x, (PerfdLat.dualBaseChange k'' G).inv.app n ((PerfdLat.dualBaseChange k'' G).hom.app n x) = x :=
      fun x => DFunLike.congr_fun (congrArg (fun f => Hom.app f n) (PerfdLat.dualBaseChange k'' G).inv_hom_id) x
    rw [← e x, ← e y, hxy]
  have hE : ∀ n (y : (G.dual.baseChange k').A n) (b : G.A n),
      ((PerfdLat.dualBaseChange k'' G).hom.app n (ρ.app n y)).ofConv ((G.toBase k'').app n b) =
        τ (((PerfdLat.dualBaseChange k' G).hom.app n y).ofConv ((G.toBase k').app n b)) := by
    intro n y b
    induction y using baseChange_induction k' (G := G.dual) n with
    | h0 => simp
    | h1 r χ =>
      rw [(ρ.app n).smul_map, map_smul, WithConv.ofConv_smul, LinearMap.smul_apply, map_smul, WithConv.ofConv_smul,
        LinearMap.smul_apply, hρ, dualBaseChange_toBase, dualBaseChange_toBase, smul_eq_mul, smul_eq_mul,
        map_mul]
      rfl
    | h2 z w hz hw =>
      rw [map_add, map_add, WithConv.ofConv_add, LinearMap.add_apply, map_add, WithConv.ofConv_add, LinearMap.add_apply,
        map_add, hz, hw]
  have hC : ∀ n a, ψ.app n ((G'.dual.toBase k'').app n a) = ρ.app n (φs.app n a) := by
    intro n a
    apply hinj n
    apply WithConv.ofConv_injective
    refine LinearMap.ext fun x => ?_
    induction x using baseChange_induction k'' (G := G) n with
    | h0 => simp
    | h1 r b =>
      rw [map_smul, map_smul, hE]
      congr 1
      change ((PerfdLat.dualBaseChange k'' G).hom.app n ((PerfdLat.dualBaseChange k'' G).inv.app n
        (CartierDual.map (β.app n) ((PerfdLat.dualBaseChange k'' G').hom.app n ((G'.dual.toBase k'').app n a))))).ofConv
          ((G.toBase k'').app n b) = τ (((PerfdLat.dualBaseChange k' G).hom.app n ((PerfdLat.dualBaseChange k' G).inv.app n
            (CartierDual.map (s.lift.app n) a))).ofConv ((G.toBase k').app n b))
      rw [hinv, hinv, CartierDual.map_apply, CartierDual.map_apply, hβ, dualBaseChange_toBase, toBase_app,
        SemiHom.lift_app, one_smul]
      rfl
    | h2 z w hz hw => rw [map_add, map_add, hz, hw]
  have hD' : ∀ v, lbu (B.smap hbu hb ρ v) = WittVector.map τ (lb v) := by
    intro v
    refine addHom_eq_of_basis bk (WittVector.map τ) ((lbu : _ →+ WittVector p k'').comp (B.smap hbu hb ρ))
      ((WittVector.map τ).toAddMonoidHom.comp (lb : _ →+ WittVector p k')) ?_ ?_ ?_ v
    · intro c x
      show lbu (B.smap hbu hb ρ (c • x)) = _ * lbu (B.smap hbu hb ρ x)
      rw [B.smap_smul, LinearMap.map_smul, smul_eq_mul]
    · intro c x
      simp [map_smul, smul_eq_mul, map_mul]
    · intro i
      show lbu (B.smap hbu hb ρ (bk i)) = WittVector.map τ (lb (bk i))
      rw [hbk_eq, hlb, ← B.smap_comp hbu hb hD (G.dual.toBase k') ρ (G.dual.toBase k'')
        (fun n a => (hρ n a).symm), hlbu, wittMap_comp]
  have hA : ∀ z, lb' z = lbu (B.map hbu hb' ψ z) := by
    haveI := B.free G'.dual (dual_conn h')
    haveI := B.finite G'.dual (dual_conn h')
    let b' := Module.Free.chooseBasis (WittVector p k') (B.M G'.dual (dual_conn h'))
    obtain ⟨b'', hb''⟩ := GlobalTheory.T.dieudonne_baseChange_basis p _ B k' k'' G'.dual (dual_conn h') hb' _ b'
    have key := b''.ext (f₁ := lb') (f₂ := lbu.comp (B.map hbu hb' ψ)) fun i => by
      rw [hb'', hlb', hl', LinearMap.comp_apply]
      change _ = lbu (B.smap hbu hb' (SemiHom.ofHom ψ)
        (B.smap hb' (dual_conn h') (G'.dual.toBase k'') (b' i)))
      rw [← B.smap_comp hbu hb' (dual_conn h') (G'.dual.toBase k'') (SemiHom.ofHom ψ)
        (ρ.comp (SemiHom.ofHom φs)) (fun n a => (hC n a).symm),
        B.smap_comp hbu hb (dual_conn h') (SemiHom.ofHom φs) ρ (ρ.comp (SemiHom.ofHom φs)) (fun _ _ => rfl),
        hD']
      rfl
    exact fun z => LinearMap.congr_fun key z
  rw [hl'', hA, hψ]
  exact congrArg lbu (B.smap_comp hbu hb' (dual_conn h'') (SemiHom.ofHom φt) (SemiHom.ofHom ψ)
    (SemiHom.ofHom (ψ ≫ φt)) (fun _ _ => rfl) y).symm
