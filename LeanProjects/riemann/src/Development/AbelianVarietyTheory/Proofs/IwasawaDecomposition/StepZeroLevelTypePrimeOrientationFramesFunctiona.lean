import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalChartLastStepClasses
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActsBySameIntegerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalDualEqAddSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCarryDualStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

open scoped TensorProduct in

theorem frLat_of_reindex {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {a b : ℕ} (hab : a = b) (Lb : Submodule (𝓞 E) (Fin a → E))
    (phi : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (fr : GL (Fin a) (v.adicCompletion F))
    (h : ∀ x : Fin b → v.adicCompletion F,
      (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (reL hab Lb), ∀ c, phi (y c) = x c) ↔
        ∀ c, (((reGL hab (v.adicCompletion F) fr)⁻¹ : GL (Fin b) (v.adicCompletion F)) :
          Matrix (Fin b) (Fin b) (v.adicCompletion F)).mulVec x c ∈ v.adicCompletionIntegers F)
    (t : Fin a → v.adicCompletion F) :
    (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb, ∀ c, phi (y c) = t c) ↔
      ∀ c, ((fr⁻¹ : GL (Fin a) (v.adicCompletion F)) : Matrix (Fin a) (Fin a) (v.adicCompletion F)).mulVec t c ∈
        v.adicCompletionIntegers F := by
  subst hab
  have h1 : reL (rfl : a = a) Lb = Lb := by
    ext x; simp [reL, reV]
  have h2 : reGL (rfl : a = a) (v.adicCompletion F) fr = fr := by
    ext i j; simp [reGL]
  rw [h1, h2] at h
  exact h t

theorem surj_of_card_prime {M A : Type} [AddCommGroup M] [AddCommGroup A] {T : ℕ} (hT : T.Prime) (hA : Nat.card A = T)
    (f : M →+ A) {m : M} (hm : f m ≠ 0) : Function.Surjective f := by
  haveI : Fact (Nat.card A).Prime := ⟨hA ▸ hT⟩
  rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card f.range with h | h
  · exact absurd ((AddSubgroup.eq_bot_iff_forall _).1 h _ ⟨m, rfl⟩) hm
  · exact AddMonoidHom.range_eq_top.1 h

theorem zsmul_eq_zero_iff_of_card_prime {A : Type} [AddCommGroup A] {T : ℕ} (hT : T.Prime) (hA : Nat.card A = T)
    {a : A} (ha : a ≠ 0) (k : ℤ) : k • a = 0 ↔ (T : ℤ) ∣ k := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (hA ▸ hT.ne_zero)
  have h1 : addOrderOf a = T := by
    rcases (Nat.dvd_prime hT).1 (hA ▸ addOrderOf_dvd_natCard a) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) ha
    · exact h
  rw [← h1, addOrderOf_dvd_iff_zsmul_eq_zero]

theorem exists_equiv_of_cyclic {S M A B : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup A] [Module S A]
    [AddCommGroup B] [Module S B] {T : ℕ} (hT : T.Prime) (hA : Nat.card A = T) (hB : Nat.card B = T)
    (f : M →ₗ[S] A) (g : M →ₗ[S] B) (hf : f ≠ 0) (hg : g ≠ 0) (P : M → Prop) (hfP : ∀ m, P m → f m = 0)
    (hgP : ∀ m, P m → g m = 0) (e : M) (he : ∀ t, ∃ s : S, P (t - s • e))
    (hs : ∀ s : S, ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m) :
    ∃ φ : A ≃+ B, ∀ t, φ (f t) = g t := by
  have key : ∀ t, ∃ k : ℤ, f t = k • f e ∧ g t = k • g e := by
    intro t
    obtain ⟨s, h⟩ := he t
    obtain ⟨k, h1, h2⟩ := hs s
    have a1 := hfP _ h
    have a2 := hgP _ h
    rw [map_sub, map_smul, sub_eq_zero] at a1 a2
    exact ⟨k, a1.trans (h1 _), a2.trans (h2 _)⟩
  have fe : f e ≠ 0 := fun h => hf (LinearMap.ext fun t => by obtain ⟨k, h1, -⟩ := key t; simp [h1, h])
  have ge : g e ≠ 0 := fun h => hg (LinearMap.ext fun t => by obtain ⟨k, -, h1⟩ := key t; simp [h1, h])
  have hk : f.toAddMonoidHom.ker = g.toAddMonoidHom.ker := by
    ext t
    obtain ⟨k, h1, h2⟩ := key t
    simp only [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe]
    rw [h1, h2, zsmul_eq_zero_iff_of_card_prime hT hA fe, zsmul_eq_zero_iff_of_card_prime hT hB ge]
  have sf := surj_of_card_prime hT hA f.toAddMonoidHom (m := e) fe
  have sg := surj_of_card_prime hT hB g.toAddMonoidHom (m := e) ge
  refine ⟨(QuotientAddGroup.quotientKerEquivOfSurjective _ sf).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hk).trans (QuotientAddGroup.quotientKerEquivOfSurjective _ sg)), fun t => ?_⟩
  have : (QuotientAddGroup.quotientKerEquivOfSurjective _ sf).symm (f t) = QuotientAddGroup.mk t := by
    rw [AddEquiv.symm_apply_eq]; rfl
  rw [AddEquiv.trans_apply, this]
  rfl

open scoped TensorProduct in

theorem functional_of_reindex {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →+* E) (w : HeightOneSpectrum (𝓞 F)) {a b : ℕ} (h : a = b)
    (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E) (hJ : J' = J.reindex (finCongr h) (finCongr h))
    (L : Submodule (𝓞 E) (Fin a → E)) (L' : Submodule (𝓞 E) (Fin b → E)) (hL : L' = reL h L)
    {B : Type} [AddCommGroup B] [Module (intV E w) B]
    (g' : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J' L')) →ₗ[intV E w] B)
    (hne : g' ≠ 0) (hz : ∀ x, x.1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L' → g' x = 0) :
    ∃ g : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J L)) →ₗ[intV E w] B,
      g ≠ 0 ∧ (∀ x, x.1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L → g x = 0) ∧
      ∀ (y : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (y' : GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
        (z : Fin a → E) (z' : Fin b → E) t, y' = reGL h _ y → z' = reV h E z →
        (bc (prV (E := E) w) y).1 *ᵥ t.1 = (fun i => inclE (F := F) (w.adicCompletion F) (z i)) →
        ∃ hz : ((bc (prV (E := E) w) y')⁻¹).1 *ᵥ
            (fun i => inclE (F := F) (w.adicCompletion F) (z' i)) ∈
          latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J' L')),
          g' ⟨_, hz⟩ = g t := by
  subst h
  obtain rfl : J' = J := by rw [hJ]; ext i j; simp
  obtain rfl : L' = L := by rw [hL]; ext x; simp [reL, reV]
  refine ⟨g', hne, hz, fun y y' z z' t hy hz' ht => ?_⟩
  subst hy hz'
  have h2 : reGL (rfl : a = a) _ y = y := by
    ext i j; simp [reGL]
  have ht' : ((bc (prV (E := E) w) (reGL (rfl : a = a) _ y))⁻¹).1 *ᵥ
      (fun i => inclE (F := F) (w.adicCompletion F) (reV (rfl : a = a) E z i)) = t.1 := by
    have e : (fun i => inclE (F := F) (w.adicCompletion F) (reV (rfl : a = a) E z i)) =
        fun i => inclE (F := F) (w.adicCompletion F) (z i) := rfl
    rw [h2, e, ← ht, Matrix.mulVec_mulVec]
    simp
  exact ⟨ht' ▸ t.2, congrArg g' (Subtype.ext ht')⟩

open scoped TensorProduct in
set_option maxHeartbeats 1000000 in

theorem colLevel_functional {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat)
    (hgram : sp.gram0 = 1) (p : 𝓞 E) (hp0 : p ≠ 0)
    (hL : ∀ x, x ∈ L.Lb ↔ ∀ j : Fin R.k, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = R.k → p ∣ r))
    (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal)
    (hπ : ∀ a : intV E w, (a : E ⊗[F] w.adicCompletion F) = inclE (F := F) (w.adicCompletion F) (p : E) →
      ∀ m : L.fM w h, a • m = 0)
    (hd : ∀ d : 𝓞 F, algebraMap F E (d : F) = (p : E) + sp.cm.sig (p : E) → d ∉ w.asIdeal)
    {B K : Type} [AddCommGroup B] [Module (intV E w) B] [AddCommGroup K] (hB : Nat.card B = A.T)
    (g : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)) →ₗ[intV E w] B) (gne : g ≠ 0)
    (gL : ∀ x, x.1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L.Lb → g x = 0) (ψ : B ≃+ K)
    (fz : ∀ c : C.cls 0, Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c) → K)
    (hne : ∀ c, ∃ z, fz c z ≠ 0) (hp : ∀ c z, fz c (p • z) = 0)
    (tie : ∀ c (z : Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c)) (t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb))),
      (bc (prV (E := E) w) (L.y c).1).1 *ᵥ t.1 = (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a)) →
      fz c z = ψ (g t)) :
    ∃ e : L.fM w h ≃+ K, ∀ c (z : Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c)) (t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb))),
      (bc (prV (E := E) w) (L.y c).1).1 *ᵥ t.1 = (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a)) →
      fz c z = e (L.fT w h t) := by
  have hTp := A.T_prime
  have hinv : ∀ x, sp.cm.sig (sp.cm.sig x) = x := fun x => star_star x
  have hfix : ∀ x, sp.cm.sig x = x → x ∈ (algebraMap F E).range := fun x hx => (sp.cm.fixed x).1 hx
  have hgπ : ∀ a : intV E w, (a : E ⊗[F] w.adicCompletion F) = inclE (F := F) (w.adicCompletion F) (p : E) →
      ∀ m : B, a • m = 0 := by
    intro a ha m
    have hc := L.y_bij.2 (Quotient.mk'' 1)
    obtain ⟨c, -⟩ := hc
    obtain ⟨z, hq⟩ := hne c
    have hzd : sp.crd0 z.1 ∈ dualSet (sp.cm.sig : E →+* E) sp.gram0 (sp.crdLat0 (clsLat 0 c)) := by
      rintro x ⟨x0, hx0, rfl⟩
      have h1 : (sp.X 0).hT x0 z.1 ∈ (1 : Submodule (𝓞 E) E) := by
        have := z.2
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf] at this
        exact this x0 hx0
      rw [sp.hermitianForm_base_coordinates] at h1
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
      exact ⟨r, hr⟩
    have hm := GlobalTheory.T.unitary_maps_latS_dual F E sp.cm.sig w R.k sp.gram0 L.Lb p hgram hp0 hL _ (L.y c).1 (L.y c).2 (L.y_lat c) _ hzd
    have ht : (bc (prV (E := E) w) (L.y c).1).1 *ᵥ (((bc (prV (E := E) w) (L.y c).1)⁻¹).1 *ᵥ
          (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a))) =
        (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have t1 := tie c z ⟨_, hm⟩ ht
    have t2 := tie c (p • z) (a • ⟨_, hm⟩) (by
      have e1 : ∀ x : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)), (a • x).1 = (a : E ⊗[F] w.adicCompletion F) • x.1 := fun x => rfl
      rw [e1, Matrix.mulVec_smul, ht, ha]
      funext i
      have e2 : ((p • z : Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c)) : (sp.X 0).V) = (p : E) • (z : (sp.X 0).V) :=
        (algebraMap_smul E p (z : (sp.X 0).V)).symm
      rw [e2, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul])
    rw [hp, map_smul] at t2
    have t3 := (AddEquiv.map_eq_zero_iff _).1 t2.symm
    have t4 : g ⟨_, hm⟩ ≠ 0 := fun h0 => hq (by rw [t1, h0, map_zero])
    obtain ⟨k, rfl⟩ := surj_of_card_prime hTp hB (zmultiplesHom _ (g ⟨_, hm⟩)) (m := 1) (by simpa using t4) m
    rw [zmultiplesHom_apply, smul_comm, t3, smul_zero]
  have hex := GlobalTheory.T.exists_latS_eq_of_lattice_last_coord_dvd F E sp.cm.sig w R.k sp.gram0 L.Lb p hgram hp0 hL hinv
  obtain ⟨e, he⟩ := hex
  have hex := exists_equiv_of_cyclic hTp (L.fM_card w h) hB (L.fT w h) g (L.fT_ne w h) gne
    (fun x => x.1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L.Lb) (L.fT_L w h) gL e he
    (GlobalTheory.T.acts_by_same_integer_statement F E sp.cm.sig w hinv hfix _ hTp h p hd _ _ (L.fM_card w h) hB hπ hgπ)
  obtain ⟨φ, hφ⟩ := hex
  refine ⟨φ.trans ψ, fun c z t ht => ?_⟩
  rw [tie c z t ht, AddEquiv.trans_apply, hφ]

open scoped TensorProduct in
set_option maxHeartbeats 1000000 in

theorem stepZeroLevel_functional_residueField {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) (hH : CarH H F) (hT : CarT H F A) (u : D.what₂.Word)
    (hgram : D.sp.gram0 = 1)
    (hL : ∀ x, x ∈ (H.lev0 u).Lb ↔ ∀ j : Fin D.R.k, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = D.R.k → (A u).piU ∣ r))
    (v : (D.mem u).A.vT) (w : HeightOneSpectrum (𝓞 D.host.F)) (hw : w = ((F u).atT.eV v).1)
    (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal)
    (hπ : ∀ a : intV D.host.E w, (a : D.host.E ⊗[D.host.F] w.adicCompletion D.host.F) =
      inclE (F := D.host.F) (w.adicCompletion D.host.F) ((A u).piU : D.host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) :
    ∃ e : (H.lev0 u).fM w h ≃+ (D.mem u).A.Fv v, ∀ (c : (D.mem u).C.cls 0) (z : Formalism.L2.Herm.Ld D u 0 c)
      (t : latS (F := D.host.F) (w.adicCompletion D.host.F) (intV D.host.E w) (Submodule.span (𝓞 D.host.E) (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb))),
      (bc (prV (E := D.host.E) w) ((H.lev0 u).y c).1).1 *ᵥ t.1 =
        (fun a => inclE (F := D.host.F) (w.adicCompletion D.host.F) (D.sp.crd0 z.1 a)) →
      (D.fm u).fv 0 v c ((A u).pr 0 v c z) = e ((H.lev0 u).fT w h t) := by
  subst hw
  have hc := hH.car0 u
  have hTp := (D.mem u).A.T_prime
  have hex := functional_of_reindex (F := D.host.F) (D.sp.cm.sig : D.host.E →+* D.host.E) ((F u).atT.eV v).1
    (rank_eq_first_level D.R) D.sp.gram0 (gramN D 0 (Nat.zero_le _)) (by ext i j; rfl) (H.lev0 u).Lb ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb hc.Lb_eq
    (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT _ ((F u).atT.eV v).2)
    (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_ne _ _) (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_L _ _)
  obtain ⟨g, gne, gL, hg⟩ := hex
  have hB := ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_card _ ((F u).atT.eV v).2
  have tie : ∀ (c : (D.mem u).C.cls 0) (z : Formalism.L2.Herm.Ld D u 0 c)
      (t : latS (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F) (intV D.host.E ((F u).atT.eV v).1) (Submodule.span (𝓞 D.host.E) (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb))),
      (bc (prV (E := D.host.E) ((F u).atT.eV v).1) ((H.lev0 u).y c).1).1 *ᵥ t.1 =
        (fun a => inclE (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F) (D.sp.crd0 z.1 a)) →
      (D.fm u).fv 0 v c ((A u).pr 0 v c z) = (F u).fMe 0 (Nat.zero_le _) (Or.inl rfl) v (g t) := by
    intro c z t ht
    have hz' := crdN_mem_Ld u 0 (Nat.zero_le _) c z
    have e3 : crdN D 0 (Nat.zero_le _) z.1 = reV (rank_eq_first_level D.R) D.host.E (D.sp.crd0 z.1) := by
      funext a; rfl
    have hex := hg ((H.lev0 u).y c).1 (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1 _ _ t (hc.y_eq c) e3 ht
    obtain ⟨hz, e0⟩ := hex
    have e1 := (F u).fv 0 (Nat.zero_le _) (Or.inl rfl) v c ⟨_, hz'⟩ hz
    have e2 := hT.pr u 0 (Nat.zero_le _) v c z ⟨_, hz'⟩ rfl
    exact (congrArg (fun p => (D.fm u).fv 0 v c p) e2.symm).trans (e1.trans (congrArg _ e0))
  have hp0 : (A u).piU ≠ 0 := by
    intro h0
    have := (A u).piU_norm
    rw [h0] at this
    exact hTp.ne_zero (by simpa using this.symm)
  have hd : ∀ d : 𝓞 D.host.F, algebraMap D.host.F D.host.E (d : D.host.F) =
      ((A u).piU : D.host.E) + D.sp.cm.sig ((A u).piU : D.host.E) → d ∉ ((F u).atT.eV v).1.asIdeal := by
    intro d hd hmem
    have h1 := ((F u).atT.res_v v d).1 hmem
    refine (F u).atT.res_conj v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d - (F u).atT.piU) ?_ ?_
    · rw [hT.piU u, ← Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D]
      push_cast
      rw [sub_eq_iff_eq_add']
      exact hd
    · rw [map_sub, h1, (F u).atT.res_pi, sub_zero]
  have hne : ∀ c, ∃ z : Formalism.L2.Herm.Ld D u 0 c, (D.fm u).fv 0 v c ((A u).pr 0 v c z) ≠ 0 := by
    intro c
    by_contra hn
    push Not at hn
    refine (D.fm u).fv_ne 0 v c (LinearMap.ext fun q => ?_)
    obtain ⟨z, rfl⟩ := (A u).pr_surj 0 (Nat.zero_le _) v c q
    exact hn z
  have hp : ∀ c (z : Formalism.L2.Herm.Ld D u 0 c), (D.fm u).fv 0 v c ((A u).pr 0 v c ((A u).piU • z)) = 0 := by
    intro c z
    have hres : (A u).res v (A u).piU = 0 := by
      rw [← RingHom.mem_ker, (A u).res_ker]; exact (A u).Pv_pi v
    rw [(A u).pr_smul, hres, zero_smul, map_zero]
  exact colLevel_functional (H.lev0 u) hgram (A u).piU hp0 hL _ h hπ hd hB g gne gL
    ((F u).fMe 0 (Nat.zero_le _) (Or.inl rfl) v) (fun c z => (D.fm u).fv 0 v c ((A u).pr 0 v c z)) hne hp tie

set_option maxHeartbeats 4000000 in

theorem intV_coe_eq_inclE_of_T_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → ∀ u, ∃ x : Formalism.L2.Herm.ColLevelX (H.lev0 u) (fun x => x ∈ (I.rec7 l Z).host.K) (A u).piU (H.vT u) (fun v c z => ((I.rec7 l Z).fm u).fv 0 v c ((A u).pr 0 v c z)), x.piG = X.piG := by
  intro B X I hOk hP l Z H F A hS hH hT hπ u
  have hpi := (hS u).1.gl.piG
  obtain ⟨-, -, -, hN⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hOk hP l Z
  obtain ⟨hgram, -, -⟩ := hN 0 (Nat.zero_le _)
  have hgram0 : (I.rec7 l Z).sp.gram0 = 1 := by
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun hgram (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)) (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b)
    have e : (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a = Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b) ↔ a = b := by simp [Fin.ext_iff]
    simp only [Matrix.one_apply, e] at this
    rw [Matrix.one_apply]
    exact this
  obtain ⟨k, hk⟩ := (hS u).1.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb := (hH.car0 u).Lb_eq
  have hpU : (A u).piU = X.piT u := (hT.piU u).symm.trans (hS u).1.piU
  have hL : ∀ x, x ∈ (H.lev0 u).Lb ↔ ∀ j : Fin (I.rec7 l Z).R.k, ∃ r : 𝓞 (I.rec7 l Z).host.E,
      x j = (r : (I.rec7 l Z).host.E) ∧ (j.1 + 1 = (I.rec7 l Z).R.k → (A u).piU ∣ r) := by
    intro x
    have e1 : x ∈ (H.lev0 u).Lb ↔ reV (rank_eq_first_level (I.rec7 l Z).R) _ x ∈ ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb := by
      rw [hLb]
      constructor
      · exact fun h => ⟨x, h, rfl⟩
      · rintro ⟨y, hy, e⟩
        have : y = x := (reV (rank_eq_first_level (I.rec7 l Z).R) _).injective e
        exact this ▸ hy
    rw [hpU]
    refine e1.trans ((hk.lb () _).trans ?_)
    constructor
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _))⟩
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _).symm)⟩
  choose e he using fun w h => stepZeroLevel_functional_residueField H F A hH hT u hgram0 hL ((H.vT u).symm ⟨w, h⟩) w
    (by rw [hH.eV u, Equiv.apply_symm_apply]) h (hπ u w h)
  refine ⟨{ piG := X.piG, piG_K := ?_, piG_norm := ?_, splitG_pi := ?_, splitG_alg := ?_, frG_lat := ?_, fM_pi := hπ u, fMe := e, fv0 := he }, rfl⟩
  · intro i; have h := (F u).gl_K i; rw [hpi] at h; exact h
  · intro i; have h := (F u).gl.piG_norm i; rw [hpi] at h; exact h
  · intro i v hv; have h := (F u).gl.sp_pi i v hv; rw [hpi, hH.sp u] at h; exact h
  · intro i v hv a; have h := (F u).gl.sp_alg i v hv a; rw [hH.sp u] at h; exact h
  · intro i v hv t
    have h := (F u).glev0.fr_lat i v hv
    rw [(hH.car0 u).Lb_eq, hH.fr0 u] at h
    have hphi : (F u).gl.phi i v hv = (RingHom.fst _ _).comp ((H.lev0 u).splitG i v hv).toRingHom := by
      simp only [GLoc.phi, hH.sp u]
    rw [hphi] at h
    exact frLat_of_reindex (rank_eq_first_level _) _ _ _ h t

end GlobalTheory.Mem.Col2.TC
