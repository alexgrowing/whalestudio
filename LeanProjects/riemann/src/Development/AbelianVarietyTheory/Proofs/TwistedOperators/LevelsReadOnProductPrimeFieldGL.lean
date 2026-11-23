import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelsProd

section Loc
variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}

def rx (κ : Type) [CommRing κ] (π : Equiv.Perm (Fin r)) : GL (Fin r) κ ≃* GL (Fin r) κ :=
  Units.mapEquiv (Matrix.reindexAlgEquiv κ κ π.symm).toRingEquiv.toMulEquiv

theorem rx_apply (π : Equiv.Perm (Fin r)) (u : GL (Fin r) κ) (a c : Fin r) :
    (rx κ π u).val a c = u.val (π a) (π c) := rfl

theorem rx_conj (π : Equiv.Perm (Fin r)) : ∃ c : GL (Fin r) κ, ∀ u, rx κ π u = c * u * c⁻¹ := by
  refine ⟨⟨π.toPEquiv.toMatrix, π.symm.toPEquiv.toMatrix, ?_, ?_⟩, fun u => ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  · ext a c
    rw [rx_apply]
    simp [Units.inv_mk, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]

def MemK (b : Bool) (s k : ℕ) (u : Fin r → Fin r → κ) : Prop :=
  ((∀ a, u a a = 1) ∧ ∀ a c, c < a → u a c = 0) ∧
    (b = true → ∀ a c : Fin r, s ≤ a → (a : ℕ) < s + k → (c : ℕ) = s + k → u a c = 0)

def EdK (b : Bool) (s k : ℕ) (a c : Fin r) : Prop :=
  if b = true then
    ((c : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ s ∧ ¬ (0 < k ∧ (a : ℕ) + 1 = s + k)) ∨ ((a : ℕ) + 1 = s ∧ (c : ℕ) = s + k)
  else (c : ℕ) = a + 1

open Classical in

def sumK (b : Bool) (s k : ℕ) (u : Fin r → Fin r → κ) : κ := ∑ a, ∑ c, if EdK b s k a c then u a c else 0

theorem memK_map (e : κ ≃+* κ') (b : Bool) (s k : ℕ) (u : Fin r → Fin r → κ) :
    MemK b s k (fun a c => e (u a c)) ↔ MemK b s k u := by
  simp [MemK]

theorem sumK_map (e : κ ≃+* κ') (b : Bool) (s k : ℕ) (u : Fin r → Fin r → κ) :
    sumK b s k (fun a c => e (u a c)) = e (sumK b s k u) := by
  unfold sumK
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem mem_unip_iff (u : GL (Fin r) κ) :
    u ∈ unip κ r ↔ (∀ a, u.val a a = 1) ∧ ∀ a c, c < a → u.val a c = 0 := by
  simp only [unip, blockTri, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq,
    Matrix.BlockTriangular]
  constructor
  · rintro ⟨hb, hd⟩
    exact ⟨hd, fun a c hca => hb hca⟩
  · rintro ⟨hd, hl⟩
    exact ⟨fun a c hca => hl a c hca, hd⟩

theorem mem_unip_memK (s k : ℕ) (u : GL (Fin r) κ) : u ∈ unip κ r ↔ MemK false s k u.val := by
  rw [mem_unip_iff]
  simp [MemK]

theorem mem_unipSym_memK (s k : ℕ) (u : GL (Fin r) κ) : u ∈ unipSym κ r s k ↔ MemK true s k u.val := by
  unfold unipSym unipCol
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq, mem_unip_iff, MemK]
  simp

theorem edgeSum_sup (s k : ℕ) (u : GL (Fin r) κ) : edgeSum supEdge u = sumK false s k u.val := by
  unfold edgeSum supEdge sumK EdK
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [Bool.false_eq_true, if_false]
  split_ifs <;> simp_all

theorem edgeSum_sym (s k : ℕ) (hk : 0 < k) (u : GL (Fin r) κ) : edgeSum (symEdge s k) u = sumK true s k u.val := by
  unfold edgeSum symEdge sumK EdK
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  have e : ∀ x : ℕ, (¬ (0 < k ∧ x = s + k)) ↔ x ≠ s + k := fun x => by simp [hk]
  simp only [e, ↓reduceIte]
  by_cases h : ((c : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ s ∧ (a : ℕ) + 1 ≠ s + k) ∨ ((a : ℕ) + 1 = s ∧ (c : ℕ) = s + k)
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]

end Loc

theorem ofLocal_chi {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* ℂˣ)
    (x : (Subgroup.pi Set.univ Hl : Subgroup (G0 Pg r))) :
    (((LevelP.ofLocal Hl cl).chi x : ℂˣ) : ℂ) = ∏ PP : Pg, ((cl PP (LevelP.prj Hl PP x) : ℂˣ) : ℂ) := by
  unfold LevelP.ofLocal
  simp only [MonoidHom.finset_prod_apply, MonoidHom.comp_apply]
  push_cast
  rfl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem k_pos (S : Ranks) : 0 < S.k := by
  have h := S.m_add_three_le_k
  omega

theorem rS_add_k_lt (S : Ranks) : S.rS + S.k < S.r := by
  have h := S.two_le_m
  unfold Ranks.rS Ranks.r
  omega

theorem levels_entries (h : R.grp_levels F) (b : Bool) :
    ∃ (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (π : Equiv.Perm (Fin D.R.r)), IsGenericPsi R.Pg ψ0 ∧
      (∀ g, g ∈ (R.levR F b).H ↔ ∀ PP, MemK b D.R.rS D.R.k fun a c => (g PP).val (π a) (π c)) ∧
      ∀ g hg, (((R.levR F b).chi ⟨g, hg⟩ : ℂˣ) : ℂ) =
        ∏ PP : R.Pg, ψ0 PP.1 (sumK b D.R.rS D.R.k fun a c => (g PP).val (π a) (π c)) := by
  obtain ⟨ψ0, hψ, h0, π, hπ, hmem, hchi⟩ := h
  cases b
  · clear hchi hmem hπ
    refine ⟨ψ0, Equiv.refl _, hψ, ?_, ?_⟩
    · intro g
      rw [h0]
      unfold P0 LevelP.ofLocal
      simp only [Subgroup.mem_pi, Set.mem_univ, true_implies, Equiv.refl_apply]
      exact forall_congr' fun PP => mem_unip_memK _ _ _
    · intro g hg
      generalize hL : R.levR F false = L at hg ⊢
      rw [h0] at hL
      subst hL
      clear h0 hψ
      unfold P0
      refine (ofLocal_chi _ _ ⟨g, hg⟩).trans ?_
      refine Finset.prod_congr rfl fun PP _ => ?_
      show (ψ0 PP.1) (edgeSum supEdge (g PP)) = _
      rw [edgeSum_sup D.R.rS D.R.k]
      rfl
  · clear h0 hπ
    refine ⟨ψ0, π, hψ, ?_, ?_⟩
    · intro g
      rw [hmem]
      unfold PsharpSym LevelP.ofLocal reord
      simp only [Subgroup.mem_pi, Set.mem_univ, true_implies]
      refine forall_congr' fun PP => ?_
      rw [mem_unipSym_memK]
      exact Iff.rfl
    · intro g hg
      rw [hchi g hg ((hmem g).1 hg)]
      clear hchi hψ
      unfold PsharpSym
      refine (ofLocal_chi _ _ _).trans ?_
      refine Finset.prod_congr rfl fun PP _ => ?_
      show (ψ0 PP.1) (edgeSum (symEdge D.R.rS D.R.k) (reord π g PP)) = _
      rw [edgeSum_sym D.R.rS D.R.k (k_pos D.R)]
      rfl

def splitEq (D : D7) (π : Equiv.Perm (Fin D.R.r)) : G0g D.nd ≃* GProd D where
  toFun γ := (fun v => rx _ π (γ ⟨0, v⟩), fun v => rx _ π (γ ⟨1, v⟩))
  invFun x := fun kv => match kv with
    | ⟨0, v⟩ => (rx _ π).symm (x.1 v)
    | ⟨1, v⟩ => (rx _ π).symm (x.2 v)
  left_inv γ := by
    funext kv
    match kv with
    | ⟨0, v⟩ => simp
    | ⟨1, v⟩ => simp
  right_inv x := by
    ext : 2 <;> simp
  map_mul' γ γ' := by
    ext : 2 <;> simp

theorem levels_prod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.IsGrp F → ∀ b : Bool, ∃ (Φ : G ≃* GProd D) (L₁ : D.nd.PlG 0 → GlobalTheory.BadShare.Lev (D.host.g 0) D.R.r) (L₂ : D.nd.PlG 1 → GlobalTheory.BadShare.Lev (D.host.g 1) D.R.r), (∀ g : G, g ∈ (F.lvl b).P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) ∧ (∀ g : (F.lvl b).P, D.what₂.embLL (((F.lvl b).ψ⁻¹ g : D.what₂.LLˣ) : D.what₂.LL) = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) ∧ (∀ g : G, GlobalTheory.BadShare.AllUnip (Φ g).1 ∨ GlobalTheory.BadShare.AllUnip (Φ g).2 → ∃ (k : Fin 2) (PP : R.Pg), CharP (kP PP.1) (D.host.g k) ∧ IsNilpotent ((R.eG g PP).val - 1)) ∧ ∀ (g : G) (γ : G0g D.nd), (∀ v, γ ⟨0, v⟩ = (Φ g).1 v) → (∀ v, γ ⟨1, v⟩ = (Φ g).2 v) → D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff γ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG b
  obtain ⟨-, -, hlev, hrec, -⟩ := hG
  obtain ⟨ψ0, π, hψ, hmem, hchi⟩ := levels_entries (R := R) (F := F) hlev b
  obtain ⟨eR, plg, iso, h1, -, h3⟩ := hrec
  have hne : ∀ k, Nonempty (D.nd.PlG k) := fun k => by
    have e1 := D.nd.card_PlG k
    have e2 := D.R.two_le_m
    have e3 := D.R.m_le_f
    unfold Ranks.f Ranks.n at e1
    exact Fintype.card_pos_iff.mp (by omega)

  have hR : ∀ (κ : Type) [CommRing κ] (u : GL (Fin D.R.r) κ),
      ((rx κ π u : GL (Fin D.R.r) κ) : Matrix (Fin D.R.r) (Fin D.R.r) κ) = fun a c => u.val (π a) (π c) :=
    fun κ _ u => funext fun a => funext fun c => rx_apply π u a c

  have hX : ∀ (g : G) (kv : (Σ k : Fin 2, D.nd.PlG k)),
      (fun a c => (R.eG g (plg kv)).val (π a) (π c)) = fun a c => iso kv ((eR g kv).val (π a) (π c)) := by
    intro g kv
    rw [h3]
    rfl

  have hψne : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      ((ψ0 (plg kv).1).compAddMonoidHom (iso kv).toAddMonoidHom)⁻¹ ≠ 1 := by
    intro kv h
    apply hψ (plg kv).1 (plg kv).2
    ext x
    have := congrArg (fun χ : AddChar (ZMod (D.host.g kv.1)) ℂ => χ (-((iso kv).symm x))) h
    simpa using this
  have hmemG : ∀ g : G, g ∈ (F.lvl b).P ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      MemK b D.R.rS D.R.k (fun a c => (eR g kv).val (π a) (π c)) := by
    intro g
    have e : g ∈ (F.lvl b).P ↔ R.eG g ∈ (R.levR F b).H := by
      unfold RealDat.levR levPOf
      simp [Subgroup.mem_comap]
    refine (e.trans (hmem _)).trans (plg.forall_congr_right.symm.trans (forall_congr' fun kv => ?_))
    exact (Iff.of_eq (congrArg (MemK b D.R.rS D.R.k) (hX g kv))).trans (memK_map (iso kv) b D.R.rS D.R.k _)
  have hchiL : ∀ (p : ℕ) [Fact p.Prime] (L' : GlobalTheory.BadShare.Lev p D.R.r) (x : GL (Fin D.R.r) (ZMod p)),
      (∀ a, L'.co a = 1) → L'.chi x = L'.ψ (sumK L'.sharp L'.s L'.k x.val) := by
    intro p _ L' x hco
    unfold GlobalTheory.BadShare.Lev.chi GlobalTheory.BadShare.Lev.Edge sumK EdK
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hco a, Units.val_one, one_mul]
  let L : ∀ k : Fin 2, D.nd.PlG k → GlobalTheory.BadShare.Lev (D.host.g k) D.R.r := fun k v =>
    { sharp := b, s := D.R.rS, k := D.R.k, hk := rS_add_k_lt D.R,
      ψ := ((ψ0 (plg ⟨k, v⟩).1).compAddMonoidHom (iso ⟨k, v⟩).toAddMonoidHom)⁻¹,
      hψ := hψne ⟨k, v⟩, co := fun _ => 1 }
  refine ⟨eR.trans (splitEq D π), L 0, L 1, ?_, ?_, ?_, ?_⟩
  · intro g
    rw [hmemG g, Sigma.forall, Fin.forall_fin_two]
    refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun v => ?_)
    · show _ ↔ MemK b D.R.rS D.R.k (rx _ π (eR g ⟨0, v⟩)).val
      rw [hR]
    · show _ ↔ MemK b D.R.rS D.R.k (rx _ π (eR g ⟨1, v⟩)).val
      rw [hR]
  · rintro ⟨g, hg⟩
    have hg' : R.eG g ∈ (R.levR F b).H := by
      unfold RealDat.levR levPOf
      simpa [Subgroup.mem_comap] using hg
    have hl : ((R.levR F b).chi ⟨R.eG g, hg'⟩ : ℂ) = D.what₂.embLL (((F.lvl b).ψ ⟨g, hg⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have hψg : ∀ x : (F.lvl b).P, (x : G) = g → (F.lvl b).ψ x = (F.lvl b).ψ ⟨g, hg⟩ := by
        rintro x rfl
        rfl
      unfold RealDat.levR levPOf
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
        hψg (R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P ⟨R.eG g, hg'⟩) (R.eG.symm_apply_apply g)]
      rfl
    have hc := hchi (R.eG g) hg'
    rw [hl] at hc
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hc, ← Finset.prod_inv_distrib,
      ← plg.prod_comp, Fintype.prod_sigma, Fin.prod_univ_two]
    congr 1
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [hchiL _ (L 0 v) _ (fun _ => rfl)]
      show _ = ((ψ0 (plg ⟨0, v⟩).1).compAddMonoidHom (iso ⟨0, v⟩).toAddMonoidHom)⁻¹
        (sumK b D.R.rS D.R.k (rx _ π (eR g ⟨0, v⟩)).val)
      rw [AddChar.inv_apply', AddChar.compAddMonoidHom_apply, hR, hX g ⟨0, v⟩, sumK_map]
      rfl
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [hchiL _ (L 1 v) _ (fun _ => rfl)]
      show _ = ((ψ0 (plg ⟨1, v⟩).1).compAddMonoidHom (iso ⟨1, v⟩).toAddMonoidHom)⁻¹
        (sumK b D.R.rS D.R.k (rx _ π (eR g ⟨1, v⟩)).val)
      rw [AddChar.inv_apply', AddChar.compAddMonoidHom_apply, hR, hX g ⟨1, v⟩, sumK_map]
      rfl
  · intro g hU
    have key : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), IsNilpotent ((rx _ π (eR g kv)).val - 1) →
        CharP (kP (plg kv).1) (D.host.g kv.1) ∧ IsNilpotent ((R.eG g (plg kv)).val - 1) := by
      intro kv hN
      refine ⟨charP_of_injective_ringHom (f := (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1)) (iso kv).injective _, ?_⟩
      have hN2 : IsNilpotent ((eR g kv).val - 1) := by
        have e1 : (rx _ π (eR g kv)).val - 1 =
            Matrix.reindexAlgEquiv (ZMod (D.host.g kv.1)) (ZMod (D.host.g kv.1)) π.symm ((eR g kv).val - 1) := by
          rw [map_sub, map_one]
          rfl
        rw [e1] at hN
        simpa using hN.map (Matrix.reindexAlgEquiv (ZMod (D.host.g kv.1)) (ZMod (D.host.g kv.1)) π.symm).symm
      have e2 : (R.eG g (plg kv)).val - 1 = (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1).mapMatrix ((eR g kv).val - 1) := by
        rw [map_sub, map_one, h3]
        rfl
      rw [e2]
      exact hN2.map _
    rcases hU with hU | hU
    · obtain ⟨v⟩ := hne 0
      obtain ⟨hc, hn⟩ := key ⟨0, v⟩ (hU v)
      exact ⟨0, plg ⟨0, v⟩, hc, hn⟩
    · obtain ⟨v⟩ := hne 1
      obtain ⟨hc, hn⟩ := key ⟨1, v⟩ (hU v)
      exact ⟨1, plg ⟨1, v⟩, hc, hn⟩
  · intro g γ hγ1 hγ2
    rw [h1 g]
    have hc : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
        ∃ c : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), ∀ u, rx _ π u = c * u * c⁻¹ := fun kv => rx_conj π
    choose C hC using hc
    have hk : ∀ k (v : D.nd.PlG k), γ ⟨k, v⟩ = C ⟨k, v⟩ * eR g ⟨k, v⟩ * (C ⟨k, v⟩)⁻¹ := by
      rw [Fin.forall_fin_two]
      refine ⟨fun v => ?_, fun v => ?_⟩
      · rw [hγ1 v, ← hC]
        rfl
      · rw [hγ2 v, ← hC]
        rfl
    have hγ : γ = (C : G0g D.nd) * eR g * C⁻¹ := funext fun kv => hk kv.1 kv.2
    rw [hγ, GlobalTheory.ProjComm.goodProjector_coeff_classFunction]

end GlobalTheory.LevelsProd

end
