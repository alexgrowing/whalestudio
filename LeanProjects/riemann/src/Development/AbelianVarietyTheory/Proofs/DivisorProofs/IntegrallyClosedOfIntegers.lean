import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfSandwichDatumBlockSumStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SumDatum

section Linear

variable {R X X₁ X₂ : Type*} [Semiring R] [AddCommMonoid X] [AddCommMonoid X₁] [AddCommMonoid X₂]
  [Module R X] [Module R X₁] [Module R X₂]

def splitEquiv (a₁ : X₁ →ₗ[R] X) (a₂ : X₂ →ₗ[R] X) (b₁ : X →ₗ[R] X₁) (b₂ : X →ₗ[R] X₂)
    (h₁ : ∀ x, b₁ (a₁ x) = x) (h₂ : ∀ x, b₂ (a₂ x) = x) (h₁₂ : ∀ x, b₂ (a₁ x) = 0)
    (h₂₁ : ∀ x, b₁ (a₂ x) = 0) (h : ∀ x, a₁ (b₁ x) + a₂ (b₂ x) = x) : X ≃ₗ[R] X₁ × X₂ :=
  LinearEquiv.ofLinear (b₁.prod b₂) (a₁.coprod a₂)
    (LinearMap.ext fun ⟨x, y⟩ => by simp [h₁, h₂, h₁₂, h₂₁])
    (LinearMap.ext fun x => by simp [h])

end Linear

section Fin

variable {R : Type*} [Semiring R]

variable (R) in

def appendEquiv (m n : ℕ) : ((Fin m → R) × (Fin n → R)) ≃ₗ[R] (Fin (m + n) → R) where
  toFun x := Fin.append x.1 x.2
  invFun z := (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))
  map_add' x y := by
    funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  map_smul' c x := by
    funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  left_inv x := by simp
  right_inv z := Fin.append_castAdd_natAdd

theorem appendEquiv_apply {m n : ℕ} (x : (Fin m → R) × (Fin n → R)) :
    appendEquiv R m n x = Fin.append x.1 x.2 := rfl

theorem appendEquiv_symm_apply {m n : ℕ} (z : Fin (m + n) → R) :
    (appendEquiv R m n).symm z = (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j)) :=
  rfl

theorem append_eq_zero_iff {m n : ℕ} (x : Fin m → R) (y : Fin n → R) :
    Fin.append x y = 0 ↔ x = 0 ∧ y = 0 :=
  ((appendEquiv R m n).map_eq_zero_iff (x := (x, y))).trans Prod.mk_eq_zero

theorem comp_append {α β : Type*} {m n : ℕ} (f : α → β) (x : Fin m → α) (y : Fin n → α) :
    (fun i => f (Fin.append x y i)) = Fin.append (fun i => f (x i)) (fun j => f (y j)) := by
  funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp

theorem single_castAdd {m n : ℕ} (i : Fin m) :
    (Pi.single (Fin.castAdd n i) 1 : Fin (m + n) → R) = Fin.append (Pi.single i 1) 0 := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [Pi.single_apply]
  · have hne : Fin.natAdd m j ≠ Fin.castAdd n i := fun h' => by
      have h'' := congrArg Fin.val h'
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h''
      have := i.isLt
      omega
    simp [Pi.single_apply, hne]

theorem single_natAdd {m n : ℕ} (j : Fin n) :
    (Pi.single (Fin.natAdd m j) 1 : Fin (m + n) → R) = Fin.append 0 (Pi.single j 1) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · have hne : Fin.castAdd n i ≠ Fin.natAdd m j := fun h' => by
      have h'' := congrArg Fin.val h'
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h''
      have := i.isLt
      omega
    simp [Pi.single_apply, hne]
  · simp [Pi.single_apply]

end Fin

end GlobalTheory.SumDatum

namespace GlobalTheory.SumDatum

section Groups

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {G G₁ G₂ : PDivGroup p O}
  (i₁ : G₁ ⟶ G) (i₂ : G₂ ⟶ G) (q₁ : G ⟶ G₁) (q₂ : G ⟶ G₂)

include i₁ i₂ in

theorem exists_tateSplit (h₁ : i₁ ≫ q₁ = 𝟙 _) (h₂ : i₂ ≫ q₂ = 𝟙 _) (h₁₂ : i₁ ≫ q₂ = 0)
    (h₂₁ : i₂ ≫ q₁ = 0) (h : q₁ ≫ i₁ + q₂ ≫ i₂ = 𝟙 _) :
    ∃ T : G.Tate ≃ₗ[ℤ_[p]] G₁.Tate × G₂.Tate,
      (∀ t, T t = (tateMap G G₁ O q₁ t, tateMap G G₂ O q₂ t)) ∧
      ∀ a b, T.symm (a, b) = tateMap G₁ G O i₁ a + tateMap G₂ G O i₂ b :=
  ⟨splitEquiv (tateMap G₁ G O i₁) (tateMap G₂ G O i₂) (tateMap G G₁ O q₁) (tateMap G G₂ O q₂)
    (fun x => by rw [← tateMap_comp, h₁, tateMap_id])
    (fun x => by rw [← tateMap_comp, h₂, tateMap_id])
    (fun x => by rw [← tateMap_comp, h₁₂, map_zero, LinearMap.zero_apply])
    (fun x => by rw [← tateMap_comp, h₂₁, map_zero, LinearMap.zero_apply])
    (fun x => by
      have := LinearMap.congr_fun (congrArg (tateMap G G O) h) x
      rwa [map_add, LinearMap.add_apply, tateMap_comp, tateMap_comp, tateMap_id] at this),
    fun _ => rfl, fun _ _ => rfl⟩

include i₁ i₂ in

theorem exists_lieSplit (h₁ : i₁ ≫ q₁ = 𝟙 _) (h₂ : i₂ ≫ q₂ = 𝟙 _) (h₁₂ : i₁ ≫ q₂ = 0)
    (h₂₁ : i₂ ≫ q₁ = 0) (h : q₁ ≫ i₁ + q₂ ≫ i₂ = 𝟙 _) :
    ∃ L : G.Lie ≃ₗ[O] G₁.Lie × G₂.Lie, ∀ x, L x = (lieMap G G₁ q₁ x, lieMap G G₂ q₂ x) :=
  ⟨splitEquiv (lieMap G₁ G i₁) (lieMap G₂ G i₂) (lieMap G G₁ q₁) (lieMap G G₂ q₂)
    (fun x => by
      have := LinearMap.congr_fun (lieMap_comp i₁ q₁) x
      rw [h₁, lieMap_id] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (lieMap_comp i₂ q₂) x
      rw [h₂, lieMap_id] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (lieMap_comp i₁ q₂) x
      rw [h₁₂, map_zero] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (lieMap_comp i₂ q₁) x
      rw [h₂₁, map_zero] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (congrArg (lieMap G G) h) x
      rw [map_add, lieMap_comp, lieMap_comp, lieMap_id] at this; exact this),
    fun _ => rfl⟩

include i₁ i₂ in

theorem exists_omegaDualSplit (h₁ : i₁ ≫ q₁ = 𝟙 _) (h₂ : i₂ ≫ q₂ = 𝟙 _) (h₁₂ : i₁ ≫ q₂ = 0)
    (h₂₁ : i₂ ≫ q₁ = 0) (h : q₁ ≫ i₁ + q₂ ≫ i₂ = 𝟙 _) :
    ∃ W : G.dual.omega ≃ₗ[O] G₁.dual.omega × G₂.dual.omega,
      ∀ w, W w = (omegaDualMap G G₁ q₁ w, omegaDualMap G G₂ q₂ w) :=
  ⟨splitEquiv (omegaDualMap G₁ G i₁) (omegaDualMap G₂ G i₂) (omegaDualMap G G₁ q₁)
    (omegaDualMap G G₂ q₂)
    (fun x => by
      have := LinearMap.congr_fun (omegaDualMap_comp i₁ q₁) x
      rw [h₁, omegaDualMap_id] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (omegaDualMap_comp i₂ q₂) x
      rw [h₂, omegaDualMap_id] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (omegaDualMap_comp i₁ q₂) x
      rw [h₁₂, map_zero] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (omegaDualMap_comp i₂ q₁) x
      rw [h₂₁, map_zero] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (congrArg (omegaDualMap G G) h) x
      rw [map_add, omegaDualMap_comp, omegaDualMap_comp, omegaDualMap_id] at this; exact this),
    fun _ => rfl⟩

end Groups

section Datum

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} {h₁ h₂ : ℕ}
  {D : Datum ε (h₁ + h₂) ℤ_[p]} {D₁ : Datum ε h₁ ℤ_[p]} {D₂ : Datum ε h₂ ℤ_[p]}

theorem append_mem_fil_iff (hb : ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y))
    (x : Fin h₁ → O) (y : Fin h₂ → O) : Fin.append x y ∈ D.Fil ↔ x ∈ D₁.Fil ∧ y ∈ D₂.Fil := by
  simp only [Datum.Fil, LinearMap.mem_ker, hb, append_eq_zero_iff]

theorem split_mem_fil (hb : ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y))
    (z : Fin (h₁ + h₂) → O) (hz : z ∈ D.Fil) :
    (fun i => z (Fin.castAdd h₂ i)) ∈ D₁.Fil ∧ (fun j => z (Fin.natAdd h₁ j)) ∈ D₂.Fil :=
  (append_mem_fil_iff hb _ _).1 (by rwa [Fin.append_castAdd_natAdd])

theorem exists_filSplit (hb : ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y)) :
    ∃ F : D.Fil ≃ₗ[O] D₁.Fil × D₂.Fil,
      ∀ u v, (F.symm (u, v) : Fin (h₁ + h₂) → O) = Fin.append u.1 v.1 :=
  ⟨{ toFun := fun z => (⟨_, (split_mem_fil hb z.1 z.2).1⟩, ⟨_, (split_mem_fil hb z.1 z.2).2⟩)
     invFun := fun w => ⟨Fin.append w.1.1 w.2.1, (append_mem_fil_iff hb _ _).2 ⟨w.1.2, w.2.2⟩⟩
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     left_inv := fun z => Subtype.ext Fin.append_castAdd_natAdd
     right_inv := fun w => by ext i <;> simp }, fun _ _ => rfl⟩

variable (D₁ D₂) in

def quotProj : (Fin (h₁ + h₂) → O) →ₗ[O] ((Fin h₁ → O) ⧸ D₁.Fil) × ((Fin h₂ → O) ⧸ D₂.Fil) :=
  (D₁.Fil.mkQ.prodMap D₂.Fil.mkQ) ∘ₗ (appendEquiv O h₁ h₂).symm.toLinearMap

theorem exists_quotSplit (hb : ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y)) :
    ∃ Q : ((Fin (h₁ + h₂) → O) ⧸ D.Fil) ≃ₗ[O] ((Fin h₁ → O) ⧸ D₁.Fil) × ((Fin h₂ → O) ⧸ D₂.Fil),
      ∀ z, Q (D.Fil.mkQ z) = (D₁.Fil.mkQ (fun i => z (Fin.castAdd h₂ i)),
        D₂.Fil.mkQ (fun j => z (Fin.natAdd h₁ j))) := by
  have hker : D.Fil = LinearMap.ker (quotProj D₁ D₂) := by
    ext z
    rw [LinearMap.mem_ker]
    conv_lhs => rw [← Fin.append_castAdd_natAdd (f := z)]
    rw [append_mem_fil_iff hb]
    simp [quotProj, appendEquiv_symm_apply, Submodule.Quotient.mk_eq_zero]
  have hs : Function.Surjective (quotProj D₁ D₂) := by
    rintro ⟨u, v⟩
    obtain ⟨a, rfl⟩ := D₁.Fil.mkQ_surjective u
    obtain ⟨b, rfl⟩ := D₂.Fil.mkQ_surjective v
    exact ⟨Fin.append a b, by simp [quotProj, appendEquiv_symm_apply]⟩
  exact ⟨(D.Fil.quotEquivOfEq _ hker).trans ((quotProj D₁ D₂).quotKerEquivOfSurjective hs),
    fun z => rfl⟩

theorem bQuot_symm (hb : ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y))
    (Q : ((Fin (h₁ + h₂) → O) ⧸ D.Fil) ≃ₗ[O] ((Fin h₁ → O) ⧸ D₁.Fil) × ((Fin h₂ → O) ⧸ D₂.Fil))
    (hQ : ∀ z, Q (D.Fil.mkQ z) = (D₁.Fil.mkQ (fun i => z (Fin.castAdd h₂ i)),
        D₂.Fil.mkQ (fun j => z (Fin.natAdd h₁ j)))) (u) :
    bQuot D (Q.symm u) = Fin.append (bQuot D₁ u.1) (bQuot D₂ u.2) := by
  obtain ⟨q, rfl⟩ := Q.surjective u
  obtain ⟨z, rfl⟩ := D.Fil.mkQ_surjective q
  rw [LinearEquiv.symm_apply_apply, hQ]
  simp only [bQuot, Submodule.mkQ_apply, Submodule.liftQ_apply]
  conv_lhs => rw [← Fin.append_castAdd_natAdd (f := z)]
  exact hb _ _

end Datum

end GlobalTheory.SumDatum

namespace GlobalTheory.SumDatum

section Pairing

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] {ε : PreTilt O p}
  (hε : IsPrimitiveSystem ε) {h₁ h₂ : ℕ} {G G₁ G₂ : PDivGroup p O}

theorem pairingO_append (i₁ : G₁ ⟶ G) (i₂ : G₂ ⟶ G)
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin (h₁ + h₂) → ℤ_[p])) (e₁ : G₁.Tate ≃ₗ[ℤ_[p]] (Fin h₁ → ℤ_[p]))
    (e₂ : G₂.Tate ≃ₗ[ℤ_[p]] (Fin h₂ → ℤ_[p]))
    (he : ∀ a b, e.symm (Fin.append a b) = tateMap G₁ G O i₁ (e₁.symm a) +
      tateMap G₂ G O i₂ (e₂.symm b))
    (y₁ : Fin h₁ → O) (y₂ : Fin h₂ → O) (χ : G.dual.Tate) :
    pairingO hε e (Fin.append y₁ y₂) χ =
      pairingO hε e₁ y₁ (tateMap _ _ O (dualHom G₁ G i₁) χ) +
        pairingO hε e₂ y₂ (tateMap _ _ O (dualHom G₂ G i₂) χ) := by
  have hp1 : ∀ i : Fin h₁, epsPairing hε G (e.symm (Pi.single (Fin.castAdd h₂ i) 1)) χ =
      epsPairing hε G₁ (e₁.symm (Pi.single i 1)) (tateMap _ _ O (dualHom G₁ G i₁) χ) := by
    intro i
    rw [single_castAdd, he]
    simp [epsPairing, pairing_tateMap]
  have hp2 : ∀ j : Fin h₂, epsPairing hε G (e.symm (Pi.single (Fin.natAdd h₁ j) 1)) χ =
      epsPairing hε G₂ (e₂.symm (Pi.single j 1)) (tateMap _ _ O (dualHom G₂ G i₂) χ) := by
    intro j
    rw [single_natAdd, he]
    simp [epsPairing, pairing_tateMap]
  simp only [pairingO, Fin.sum_univ_add, Fin.append_left, Fin.append_right, hp1, hp2]

end Pairing

end GlobalTheory.SumDatum

namespace GlobalTheory.SumDatum

theorem integrallyClosed_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

theorem hasDatum_of_isSum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G G₁ G₂ : PDivGroup p O,
      IsSum G G₁ G₂ → HasDatum hε G₁ → HasDatum hε G₂ → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G G₁ G₂ ⟨i₁, i₂, q₁, q₂, h₁, h₂, h₁₂, h₂₁, h⟩
    ⟨D₁, e₁, fil₁, lie₁, hal₁, hb₁⟩ ⟨D₂, e₂, fil₂, lie₂, hal₂, hb₂⟩
  haveI := integrallyClosed_of_integers hv
  obtain ⟨D, hal, hbb⟩ := GlobalTheory.T.exists_ainfSandwichDatum_blockSum p C v O hv ε hε _ _ D₁ D₂
  obtain ⟨T, hT, hTs⟩ := exists_tateSplit i₁ i₂ q₁ q₂ h₁ h₂ h₁₂ h₂₁ h
  obtain ⟨L, hL⟩ := exists_lieSplit i₁ i₂ q₁ q₂ h₁ h₂ h₁₂ h₂₁ h
  obtain ⟨W, hW⟩ := exists_omegaDualSplit i₁ i₂ q₁ q₂ h₁ h₂ h₁₂ h₂₁ h
  obtain ⟨F, hF⟩ := exists_filSplit hbb
  obtain ⟨Q, hQ⟩ := exists_quotSplit hbb
  let e : G.Tate ≃ₗ[ℤ_[p]] (Fin (G₁.height + G₂.height) → ℤ_[p]) :=
    T ≪≫ₗ e₁.prodCongr e₂ ≪≫ₗ appendEquiv ℤ_[p] _ _
  have he : ∀ t, e t = Fin.append (e₁ (tateMap G G₁ O q₁ t)) (e₂ (tateMap G G₂ O q₂ t)) :=
    fun t => by simp [e, hT, appendEquiv_apply]
  have hes : ∀ a b, e.symm (Fin.append a b) = tateMap G₁ G O i₁ (e₁.symm a) +
      tateMap G₂ G O i₂ (e₂.symm b) := fun a b => by
    have : (appendEquiv ℤ_[p] G₁.height G₂.height).symm (Fin.append a b) = (a, b) :=
      (appendEquiv ℤ_[p] G₁.height G₂.height).symm_apply_apply (a, b)
    simp [e, this, hTs]
  have hh : G.height = G₁.height + G₂.height := by
    rw [← G.finrank_tate C, e.finrank_eq, Module.finrank_fin_fun]
  have key : ∃ (D : Datum ε (G₁.height + G₂.height) ℤ_[p])
      (e : G.Tate ≃ₗ[ℤ_[p]] (Fin (G₁.height + G₂.height) → ℤ_[p]))
      (fil : G.dual.omega ≃ₗ[O] D.Fil)
      (lie : ((Fin (G₁.height + G₂.height) → O) ⧸ D.Fil) ≃ₗ[O] G.Lie),
      (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin (G₁.height + G₂.height) → O)) ∧
        ∀ (x : G.Lie) (χ : G.dual.Tate), pairingO hε e (bQuot D (lie.symm x)) χ = x (dlog G χ) := by
    refine ⟨D, e, W ≪≫ₗ fil₁.prodCongr fil₂ ≪≫ₗ F.symm, Q ≪≫ₗ lie₁.prodCongr lie₂ ≪≫ₗ L.symm,
      fun t => ?_, fun x χ => ?_⟩
    · have ht : toO e t = Fin.append (toO e₁ (tateMap G G₁ O q₁ t))
          (toO e₂ (tateMap G G₂ O q₂ t)) := by
        show (fun i => padicToO p O (e t i)) = _
        rw [he]
        exact comp_append _ _ _
      rw [ht, hal, hal₁, hal₂, hodgeTate_tateMap, hodgeTate_tateMap]
      show _ = ((F.symm ((fil₁.prodCongr fil₂) (W (hodgeTate G t))) : D.Fil) :
        Fin (G₁.height + G₂.height) → O)
      rw [hW, LinearEquiv.prodCongr_apply, hF]
    · have hx : (Q ≪≫ₗ lie₁.prodCongr lie₂ ≪≫ₗ L.symm).symm x =
          Q.symm (lie₁.symm (lieMap G G₁ q₁ x), lie₂.symm (lieMap G G₂ q₂ x)) := by
        simp [hL]
      rw [hx, bQuot_symm hbb Q hQ, pairingO_append hε i₁ i₂ e e₁ e₂ hes, hb₁, hb₂,
        lieMap_apply, lieMap_apply, dlog_tateMap, dlog_tateMap, ← map_add]
      have hw := LinearMap.congr_fun (congrArg (omegaMap G G) h) (dlog G χ)
      rw [map_add, omegaMap_comp, omegaMap_comp, omegaMap_id] at hw
      exact congrArg x hw
  unfold HasDatum
  rw [hh]
  exact key

end GlobalTheory.SumDatum
